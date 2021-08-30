
package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Set;
import java.util.concurrent.locks.*;

public class AndroidLogger {

    private final static String USER_HOME = System.getProperty("user.home");
    private static String androidJar = "/usr/lib/android-sdk/platforms";
    private static HashSet<String> generatedFunctionNames = new HashSet<String>();
    static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator + "Android";
    static String apkPath = androidDemoPath + File.separator + "/calc.apk";
    static String outputPath = androidDemoPath + File.separator + "/Instrumented";

    private static String INT = "int";
    private static String FLOAT = "float";
    private static String CHAR = "char";
    private static String LONG = "long";
    private static String BOOLEAN = "boolean";
    private static String SHORT = "short";
    private static String BYTE = "byte";
    private static String DOUBLE = "double";
    static ReentrantLock lock = new ReentrantLock();

    public static void main(String[] args) {
        if(System.getenv().containsKey("ANDROID_HOME"))
            androidJar = System.getenv("ANDROID_HOME")+ File.separator+"platforms";
        // Clean the outputPath
        final File[] files = (new File(outputPath)).listFiles();
        if (files != null && files.length > 0) {
            Arrays.asList(files).forEach(File::delete);
        }
        // Initialize Soot
        InstrumentUtil.setupSoot(androidJar, apkPath, outputPath);
        // Find the package name of the APK
        String packageName = AndroidUtil.getPackageName(apkPath);
        SootClass counterClass = createCounterClass(packageName);
        HashMap <String, SootMethod> classNamesToReadIncrementors = new HashMap<>();
        HashMap <String, SootMethod> classNamesToWriteIncrementors = new HashMap<>();
        HashMap <String, ObjectProfilingData> classNamesToObjectData = new HashMap<>();
        HashMap <String, SootClass> namesToArrayClasses = new HashMap<>();
        ArrayWrapperCreator arrayWrapperCreator = new ArrayWrapperCreator(counterClass, packageName);

        instrumentClasses(counterClass, classNamesToReadIncrementors, classNamesToWriteIncrementors, classNamesToObjectData);
        PackManager.v().getPack("jtp").add(
            new Transform("jtp.modifyMethods", 
                new MethodModifier(namesToArrayClasses, classNamesToReadIncrementors, 
                    classNamesToWriteIncrementors, arrayWrapperCreator)
            )
        );

        PackManager.v().getPack("jtp").add(
            new Transform("jtp.recordAccesses", 
                new ObjectLoggingInjector(counterClass, namesToArrayClasses, classNamesToReadIncrementors, 
                    classNamesToWriteIncrementors, arrayWrapperCreator)
            )
        );

////        PackManager.v().getPack("jtp").add(new Transform("jtp.test", new TypeProfilingInjector(counterClass)));
////        PackManager.v().getPack("jtp").add(new Transform("jtp.myLogger", new FunctionTracker(counterClass)));
        // PRINT STAGE
        PackManager.v().getPack("jtp").add(new Transform("jtp.print", new BodyTransformer() {
            @Override
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                // First we filter out Android framework methods
                if (AndroidUtil.isAndroidMethod(b.getMethod())) {
                    return;
                }
                lock.lock();
                JimpleBody body = (JimpleBody) b;
                UnitPatchingChain units = body.getUnits();
                if (b.getMethod().isConstructor()) {
                    System.out.println("Declaring class : " + b.getMethod().getDeclaringClass().getName());
                    System.out.println(b.toString());                  

//                    Iterator<Unit> it = units.iterator();
//                    while (it.hasNext()) {
//                        Unit unit = it.next();
//                        System.out.println("\t" + unit.toString());
//                        System.out.println("\t" + unit.getClass().getName());
//                        System.out.println();
//                    }
                }
                lock.unlock();
            }
        }));

        // Run Soot packs (note that our transformer pack is added to the phase "jtp")
        PackManager.v().runPacks();
        // Write the result of packs in outputPath
        PackManager.v().writeOutput();
    }

    static void instrumentClasses(SootClass counterClass, HashMap<String,SootMethod> classNamesToReadIncrementors, 
               HashMap<String,SootMethod> classNamesToWriteIncrementors, HashMap <String, ObjectProfilingData> classNamesToObjectData) {
        lock.lock();

        HashMap<SootMethod, ObjectProfilingData> constructorsToData = new HashMap<>();
        Iterator<SootClass>libIt = Scene.v().getLibraryClasses().iterator();
        while (libIt.hasNext()) {
            SootClass currentClass = libIt.next();
            System.out.println("Library class : " + currentClass.getName());
        }
        Iterator<SootClass> classIt = Scene.v().getApplicationClasses().iterator();
        while (classIt.hasNext()) {
            SootClass currentClass = classIt.next();
            if (currentClass.getName().equals(counterClass.getName()) || currentClass.isInterface()) {
                continue;
            }
            System.out.println("Class : " + currentClass.getName());
            List<SootMethod> methods = currentClass.getMethods();
            ClassInstrumentationUtil.addObjectAccessFields(currentClass, counterClass, currentClass.getName(), classNamesToObjectData, 
                  classNamesToReadIncrementors, classNamesToWriteIncrementors);
                ObjectProfilingData data = classNamesToObjectData.get(currentClass.getName());
            for (SootMethod m : methods) {
                if (m.isConstructor()) {
                    constructorsToData.put(m, data);
                }
            }
        }
        for (SootMethod m : constructorsToData.keySet()) {
            ObjectProfilingData data = constructorsToData.get(m);
            SootField staticCounter = data.staticCounter;
            SootField serialField = data.serialField;
            SootField readsField = data.readsField;
            SootField writesField = data.writesField;
            JimpleBody body = (JimpleBody)m.retrieveActiveBody();
            ClassInstrumentationUtil.addSerialInitialization(body, 
                serialField, staticCounter, m.getDeclaringClass());
        }
        lock.unlock();
    }

    static SootClass createCounterClass(String packageName) {
        String signature = packageName + ".StaticCounter";
        SootClass counterClass = new SootClass(signature, Modifier.PUBLIC);
        counterClass.setSuperclass(Scene.v().getSootClass("java.lang.Object")); 
        counterClass.setApplicationClass();
        return counterClass;
    }

    // MethodModifier changes the parameter and return types for all methods. It replaces
    // array type with wrapper type
    static class MethodModifier extends BodyTransformer {
        HashMap <String, SootClass> namesToArrayClasses;
        HashMap <String, SootMethod> classNamesToReadIncrementors;
        HashMap <String, SootMethod> classNamesToWriteIncrementors;
        ArrayWrapperCreator arrayWrapperCreator;
        public MethodModifier(HashMap <String, SootClass> namesToArrayClasses,                
                    HashMap<String,SootMethod> classNamesToReadIncrementors,
                    HashMap<String,SootMethod> classNamesToWriteIncrementors,
                    ArrayWrapperCreator arrayWrapperCreator) {
            this.namesToArrayClasses = namesToArrayClasses;
            this.classNamesToReadIncrementors = classNamesToReadIncrementors;
            this.classNamesToWriteIncrementors = classNamesToWriteIncrementors;
            this.arrayWrapperCreator = arrayWrapperCreator;
        }

        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if (AndroidUtil.isAndroidMethod(b.getMethod())) {
                return;
            }
            lock.lock();
            JimpleBody body = (JimpleBody) b;
            UnitPatchingChain units = body.getUnits();
            Iterator<Unit> it = units.iterator();
            changeMethodParameterTypes(b.getMethod());
        }

        private void changeMethodParameterTypes(SootMethod method) {
            boolean changed = false;
            List <Type> paramTypes = method.getParameterTypes();
            for (int i = 0; i < paramTypes.size(); i++) {
                Type t = convertTypeIfArray(paramTypes.get(i));
                if (t == null) {
                    continue; 
                }
                paramTypes.set(i, t);
                changed = true;
            }
            if (changed) {
                method.setParameterTypes(paramTypes);
                System.out.println("Changed : " + method.toString());
            }
            Type t = convertTypeIfArray(method.getReturnType());
            if (t != null) {
                method.setReturnType(t);
                System.out.println("Changed return : " + method.toString());
            }
        }

        private Type convertTypeIfArray(Type t) {
            // If t is an array, convert to wrapper type and return it. Otherwise return null
            if (ClassInstrumentationUtil.isArrayType(t)) {
                Type elementType = ((ArrayType)t).getElementType();
                String wrapperName = ClassInstrumentationUtil.typeToWrapperName(elementType);
                System.out.println("Changing type " + t.toString() + " to " + wrapperName);
                SootClass wrapper;
                if (!this.namesToArrayClasses.containsKey(wrapperName)) {
                    System.out.println("wrapperName not present for method param change");
                    wrapper = this.arrayWrapperCreator.createArrayClass(elementType, 
                        this.classNamesToReadIncrementors, this.classNamesToWriteIncrementors);
                    this.namesToArrayClasses.put(wrapperName, wrapper);
                }
                else {
                    wrapper = this.namesToArrayClasses.get(wrapperName);
                }
                return wrapper.getType(); 
            }
            return null;
        }
    }

    static class ObjectLoggingInjector extends BodyTransformer {

        HashMap <String, SootMethod> classNamesToReadIncrementors;
        HashMap <String, SootMethod> classNamesToWriteIncrementors;
        HashMap <String, ObjectProfilingData> classNamesToObjectData;
        HashMap <String,SootClass> namesToArrayClasses;
        SootClass counterClass;
        ArrayWrapperCreator arrayWrapperCreator;
        public ObjectLoggingInjector(SootClass counterClass, HashMap <String,SootClass> namesToArrayClasses, 
               HashMap<String,SootMethod> classNamesToReadIncrementors,
               HashMap<String,SootMethod> classNamesToWriteIncrementors,
               ArrayWrapperCreator arrayWrapperCreator
               ) {
            this.counterClass = counterClass;
            this.classNamesToReadIncrementors = classNamesToReadIncrementors;
            this.classNamesToWriteIncrementors = classNamesToWriteIncrementors;
            this.classNamesToObjectData = new HashMap<>();
            this.namesToArrayClasses = namesToArrayClasses;
            this.arrayWrapperCreator = arrayWrapperCreator;
        }



        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if (AndroidUtil.isAndroidMethod(b.getMethod()) || b.getMethod().isConstructor()) {
                return;
            }
            if (b.getMethod().getName().equals("incReads") || b.getMethod().getName().equals("incWrites")) {
                return;
            }
            lock.lock();

            JimpleBody body = (JimpleBody) b;
            UnitPatchingChain units = body.getUnits();
            Iterator<Unit> it = units.iterator();
            ArrayList<InsertionPair<Unit>> beforePairs = new ArrayList<InsertionPair<Unit>>();
            ArrayList<InsertionPair<Unit>> swapPairs = new ArrayList<InsertionPair<Unit>>();
            System.out.println("ORIGINAL: " + body.toString());
            while (it.hasNext()) {
                Unit unit = it.next();
                if (unit instanceof JIdentityStmt) {
                    Value rhs = ((JIdentityStmt)unit).getRightOp();
                    Value lhs = ((JIdentityStmt)unit).getLeftOp();
                    if (rhs instanceof ParameterRef) {
                        // Set new types for params
                        Type t = rhs.getType();
                        if (ClassInstrumentationUtil.isArrayType(t)) {
                            Type elementType = ((ArrayType)t).getElementType();
                            System.out.println("Updating PARAM " + unit.toString());
                            SootClass wrapper = findWrapper(elementType);
                            System.out.println("\telementType " + elementType.toString());
                            System.out.println("\tWrapper type " + wrapper.getType().toString());
                            ParameterRef newParamRef = Jimple.v().newParameterRef(
                                wrapper.getType(),
                                ((ParameterRef)rhs).getIndex()
                            );
                            ((JimpleLocal)lhs).setType(wrapper.getType());
                            ((JIdentityStmt)unit).setRightOp(newParamRef);
                        }
                    }
                }
                if (unit instanceof InvokeExpr) {
                    // Analyze args to see if there are any array types. If so,
                    // get array from the wrapper and pass it
                    SootMethod calledMethod = ((InvokeExpr)unit).getMethod();
                    List<Value> args = ((InvokeExpr)unit).getArgs();
                    List <Type> paramTypes = calledMethod.getParameterTypes();
                    for (int i = 0; i < paramTypes.size(); i++) {
                        Type t = paramTypes.get(i);
                        System.out.println("\t" + args.get(i).toString() + " is type : " + t.toString());
                        if (ClassInstrumentationUtil.isArrayType(t)) {
                            Type elementType = ((ArrayType)t).getElementType();
                            SootClass wrapper = findWrapper(elementType);
                            Local arrayLocal = InstrumentUtil.generateNewLocal(body, elementType);
                            InstanceFieldRef arrayField = Jimple.v().newInstanceFieldRef(args.get(i), 
                                wrapper.getFieldByName("array").makeRef());
                            Unit arrayAssign = Jimple.v().newAssignStmt(arrayLocal, arrayField);
                            beforePairs.add(new InsertionPair<Unit>(arrayAssign, unit));
                            System.out.println("\tRetrieving array arg  for " + unit.toString());
                            ((InvokeExpr)unit).setArg(i, arrayLocal);
                        }
                    }
                }
                else if (unit instanceof JAssignStmt) {

                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (lhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)lhs, 
                            beforePairs, this.classNamesToWriteIncrementors, unit); 
                    }
                    else if (lhs instanceof JNewArrayExpr) {
                    }
                    else if (lhs instanceof JArrayRef) {
                        // Replace array writes to wrapper get function
                        arrayRefWrite(unit, lhs, rhs, beforePairs, swapPairs);
                    }
                    if (rhs instanceof JInstanceFieldRef) {
                        // Insert accsss methods
                        invokeObjectMethods((JInstanceFieldRef)rhs, 
                            beforePairs, this.classNamesToReadIncrementors, unit);
                    }
                    else if (rhs instanceof JNewArrayExpr) {
                        // Replace new array instantiation with wrapper instantiation
                        replaceNewArray(unit, lhs, rhs, beforePairs, swapPairs);
                    }
                    else if (rhs instanceof InvokeExpr) {
                        // Analyze args to see if there are any array types. If so,
                        // get array from the wrapper and pass it
                        SootMethod calledMethod = ((InvokeExpr)rhs).getMethod();
                        List<Value> args = ((InvokeExpr)rhs).getArgs();
                        List <Type> paramTypes = calledMethod.getParameterTypes();
                        System.out.println("Analyzing calledMethod args of " + calledMethod.getName());
                        for (int i = 0; i < paramTypes.size(); i++) {
                            Type t = paramTypes.get(i);
                            System.out.println("\t" + args.get(i).toString() + " is type : " + t.toString());
                            if (ClassInstrumentationUtil.isArrayType(t)) {
                                Type elementType = ((ArrayType)t).getElementType();
                                SootClass wrapper = findWrapper(elementType);
                                Local arrayLocal = InstrumentUtil.generateNewLocal(body, elementType);
                                // TODO: Check if args.get(i) is null. If so, skip
                                if (args.get(i).toString().contains("null")) {
                                    System.out.println("\tThis is null. API type : " +  args.get(i).getClass().getName());
                                }
                                InstanceFieldRef arrayField = Jimple.v().newInstanceFieldRef(args.get(i), 
                                    wrapper.getFieldByName("array").makeRef());
                                Unit arrayAssign = Jimple.v().newAssignStmt(arrayLocal, arrayField);
                                beforePairs.add(new InsertionPair<Unit>(arrayAssign, unit));
                                System.out.println("\tRetrieving array arg  for " + unit.toString());
                                ((InvokeExpr)rhs).setArg(i, arrayLocal);
                            }
                        }
                    }
                    else if (rhs instanceof JArrayRef) {
                        arrayRefRead(unit, lhs, rhs, beforePairs, swapPairs);
                    }
                }
            }
            for (InsertionPair<Unit> pair : beforePairs) {
                units.insertBefore(pair.toInsert, pair.point);
            }
            for (InsertionPair<Unit> pair : swapPairs) {
                units.swapWith(pair.point, pair.toInsert);
            }
            beforePairs.clear();
            swapPairs.clear();
            it = units.iterator();
            while (it.hasNext()) {
                Unit unit = it.next();
                System.out.println(unit.toString());
                System.out.println("\tType: " + unit.getClass().toString() + "\n");
                if (unit instanceof JAssignStmt) {
                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (!lhs.getType().equals(rhs.getType())) {
                        System.out.println("TYPES NOT EQUAL");
                        System.out.println("\tLhs Type: " + lhs.getType().toString() + "\n");
                        System.out.println("\tRhs Type: " + rhs.getType().toString() + "\n");
                        System.out.println("\t" + unit.toString());

                            // TODO: Need to initialize wrapper before writing to it
                        if (ClassInstrumentationUtil.isArrayType(lhs.getType()) && rhs.getType().toString().contains("Array")) {
                            // if lhs is an array and a wrapper type is written to it,
                            // extract the array from the wrapper and rewrite the
                            // assignment statement
                            Type elementType = ((ArrayType)lhs.getType()).getElementType();
                            String wrapperName = ClassInstrumentationUtil.typeToWrapperName(lhs.getType());
                            SootClass wrapper;
                            if (this.namesToArrayClasses.containsKey(wrapperName)) {
                                wrapper = this.namesToArrayClasses.get(wrapperName);
                            }
                            else {
                                continue;
                            }
                            Local local = InstrumentUtil.generateNewLocal(body, lhs.getType());
                            InstanceFieldRef arrayField = Jimple.v().newInstanceFieldRef(rhs, 
                                wrapper.getFieldByName("array").makeRef());
                            Unit init = Jimple.v().newAssignStmt(local, arrayField);
                            beforePairs.add(new InsertionPair<Unit>(init, unit));
                            Unit assign = Jimple.v().newAssignStmt(lhs, local);
                            swapPairs.add(new InsertionPair<Unit>(assign, unit));
                            System.out.println("\tPath 1 Inserting: " + init.toString() + "\n\t" + assign.toString() + "\n");
                        }
                        else if (ClassInstrumentationUtil.isArrayType(rhs.getType()) && lhs.getType().toString().contains("Array")) {
                            // if rhs is an array and it is written to a wrapper type on lhs,
                            // write the array directly to the wrapper's array object
                            Type elementType = ((ArrayType)rhs.getType()).getElementType();
                            String wrapperName = ClassInstrumentationUtil.typeToWrapperName(lhs.getType());
                            SootClass wrapper;
                            if (this.namesToArrayClasses.containsKey(wrapperName)) {
                                wrapper = this.namesToArrayClasses.get(wrapperName);
                            }
                            else {
                                continue;
                            }
                            Local local = InstrumentUtil.generateNewLocal(body, rhs.getType());
                            InstanceFieldRef arrayField = Jimple.v().newInstanceFieldRef(lhs, 
                                wrapper.getFieldByName("array").makeRef());
                            Unit init = Jimple.v().newAssignStmt(local, rhs);
                            beforePairs.add(new InsertionPair<Unit>(init, unit));
                            Unit assign = Jimple.v().newAssignStmt(arrayField, local);
                            swapPairs.add(new InsertionPair<Unit>(assign, unit));
                            System.out.println("\tPath 2 Inserting: \n\t\t" + init.toString() + "\t\t\n" + assign.toString() + "\n");
                        }
                    }
                }
            }
            for (InsertionPair<Unit> pair : beforePairs) {
                System.out.println("insertBefore\n\tinsert: " + pair.toInsert.toString() + "\n\tpoint: " + pair.point.toString());
                units.insertBefore(pair.toInsert, pair.point);
            }
            for (InsertionPair<Unit> pair : swapPairs) {
                System.out.println("swap\n\tinsert: " + pair.toInsert.toString() + "\n\tpoint: " + pair.point.toString());
                units.swapWith(pair.point, pair.toInsert);
            }
//            it = units.iterator();
//            while (it.hasNext()) {
//                Unit unit = it.next();
//                System.out.println(unit.toString());
//                if (unit instanceof JAssignStmt) {
//                    Value lhs = ((JAssignStmt)unit).getLeftOp();
//                    Value rhs = ((JAssignStmt)unit).getRightOp();
//                    System.out.println("\tlhs type : " + lhs.getType().toString());
//                    System.out.println("\trhs type : " + lhs.getType().toString());
//                    System.out.println("\t Types equal ? " + lhs.getType().equals(rhs.getType()) + "\n");
//                }
//            }
            System.out.println("Current class: " + b.getMethod().getDeclaringClass().getName());
            System.out.println("-------\n\n");
            System.out.println("Validating:\n" + body.toString());
            body.validate();
            lock.unlock();
        }

        private void arrayRefRead(Unit unit, Value lhs, Value rhs,
                        ArrayList<InsertionPair<Unit>>beforePairs, ArrayList<InsertionPair<Unit>>swapPairs) {
            // Replaces write to array to use set method
            Type elementType = lhs.getType();
            if (elementType.toString().contains("[]")) {
                // For now skip multidimensional arrays
                // TODO: Complete
                System.out.println("\tSkipping " + elementType);
                return;
            }
            SootClass wrapper = findWrapper(elementType);
            Value rhsLocal = ((JArrayRef)rhs).getBase();
            ((Local)rhsLocal).setType(wrapper.getType());
            SootMethod getMethod = wrapper.getMethodByName("get");
            Unit assign = Jimple.v().newAssignStmt(lhs, 
                Jimple.v().newVirtualInvokeExpr((Local)rhsLocal, 
                getMethod.makeRef(), ((JArrayRef)rhs).getIndex()));
            swapPairs.add(new InsertionPair<Unit>(assign, unit));
        }


        private void arrayRefWrite(Unit unit, Value lhs, Value rhs,
                        ArrayList<InsertionPair<Unit>>beforePairs, ArrayList<InsertionPair<Unit>>swapPairs) {
            // Replaces write to array to use set method

            Type elementType = rhs.getType();
            if (elementType.toString().contains("[]")) {
                // For now skip multidimensional arrays
                // TODO: Complete
                System.out.println("\tSkipping " + elementType);
                return;
            }
            SootClass wrapper = findWrapper(elementType);
            Value lhsLocal = ((JArrayRef)lhs).getBase();
            ((Local)lhsLocal).setType(wrapper.getType());
            SootMethod setMethod = wrapper.getMethodByName("set");
            Unit call = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr((Local)lhsLocal, 
                setMethod.makeRef(), ((JArrayRef)lhs).getIndex(), rhs));
            swapPairs.add(new InsertionPair<Unit>(call, unit));
        }

        private void replaceNewArray(Unit unit, Value lhs, Value rhs, 
                    ArrayList<InsertionPair<Unit>>beforePairs, ArrayList<InsertionPair<Unit>>swapPairs) {
            Type elementType = ((JNewArrayExpr)rhs).getBaseType();
            Value size = ((JNewArrayExpr)rhs).getSize();
            if (elementType.toString().contains("[]")) {
                // For now skip multidimensional arrays
                // TODO: Complete
                System.out.println("\tSkipping " + elementType);
                return;
            }
            SootClass wrapper = findWrapper(elementType);;
            NewExpr newExpr = Jimple.v().newNewExpr(wrapper.getType());
            ((JimpleLocal)lhs).setType(wrapper.getType());
            Unit wrapperInit = Jimple.v().newAssignStmt((JimpleLocal)lhs, newExpr);
            beforePairs.add(new InsertionPair<Unit> (wrapperInit, unit));
            Unit initCall = Jimple.v().newInvokeStmt((
                Jimple.v().newSpecialInvokeExpr((JimpleLocal)lhs, 
                wrapper.getMethodByName("<init>").makeRef(), size)
            ));
            swapPairs.add(new InsertionPair<Unit>(initCall, unit));
        }

        public void invokeObjectMethods(JInstanceFieldRef fieldRef, 
            ArrayList<InsertionPair<Unit>> beforePairs, 
            HashMap <String, SootMethod> classNamesToIncrementors, Unit unit) {
            String fullClassName = findClassName(fieldRef);
            String [] strArray = fullClassName.split("\\.");
            String className = strArray[strArray.length - 1];
            String joinedClassName = String.join("", strArray);
            SootClass currentClass = fieldRef.getField().getDeclaringClass();
            if (!classNamesToIncrementors.containsKey(joinedClassName)) {
                System.out.println(currentClass.getName() + " not present");
                return;
            }
            if (currentClass.isInterface()) {
                return;
            }
            SootMethod method = classNamesToIncrementors.get(joinedClassName);
            Local base = (Local)(fieldRef).getBase();
            Unit call = null;
            if (currentClass.isInterface()) {
                call = Jimple.v().newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(base, method.makeRef()));
            }
            else {
                call = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(base, method.makeRef()));
            }
            beforePairs.add(new InsertionPair<Unit>(call, unit));
        }

        private SootClass findWrapper(Type elementType) {
            String wrapperName = ClassInstrumentationUtil.typeToWrapperName(elementType);
            SootClass wrapper;
            if (this.namesToArrayClasses.containsKey(wrapperName)) {
                wrapper = this.namesToArrayClasses.get(wrapperName);
            }
            else {
                wrapperName = this.arrayWrapperCreator.arrayTypeToName(elementType);
                wrapper = this.arrayWrapperCreator.createArrayClass(elementType, 
                    this.classNamesToReadIncrementors, this.classNamesToWriteIncrementors);
                this.namesToArrayClasses.put(wrapperName, wrapper);
                this.namesToArrayClasses.put(wrapperName, wrapper);
                System.out.println("Creating wrapper for " + wrapperName);
            }
            return wrapper;
        }

    }




   /* ****************************************************
     The following functions are for counting reads/writes at 
     the level of TYPES
    ****************************************************** */
    static class TypeProfilingInjector extends BodyTransformer {

        SootClass counterClass;
        HashMap<String,SootMethod> classToWriteMethods = new HashMap<String, SootMethod>();
        HashMap<String,SootMethod> classToReadMethods = new HashMap<String, SootMethod>();
        public TypeProfilingInjector(SootClass counterClass) {
            this.counterClass = counterClass;
        }

        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if(AndroidUtil.isAndroidMethod(b.getMethod()))
                return;
            lock.lock();
            JimpleBody body = (JimpleBody) b;
            instrumentBody(body, this.counterClass, this.classToReadMethods, this.classToWriteMethods);
            lock.unlock();
        }
    }

    static String findClassName(JInstanceFieldRef fieldRef) {
        return fieldRef.getField()
                       .getDeclaringClass()
                       .getName();
    }

    static String findTypeName(JInstanceFieldRef fieldRef) {
        return fieldRef.getField()
                       .getType()
                       .toString();
    }

    static boolean isPrimitive(String type) {
        return type.equals(INT) || type.equals(BOOLEAN) ||
               type.equals(LONG) || type.equals(CHAR) ||
               type.equals(DOUBLE) || type.equals(FLOAT) ||
               type.equals(BYTE) || type.equals(SHORT);
    }

    // Takes a JimpleBody and iterates through the units, adding new 
    // counters as needed
    static void instrumentBody(JimpleBody body, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods) {
        UnitPatchingChain units = body.getUnits();
        Iterator<Unit> it = units.iterator();
        ArrayList<InsertionPair<Unit>> insertionPairs = new ArrayList<InsertionPair<Unit>>();
        while (it.hasNext()) {
            Unit unit = it.next();
//            System.out.println(unit.toString());
            if (unit instanceof JAssignStmt) {
//                System.out.println(unit.toString());
                Value lhs = ((JAssignStmt)unit).getLeftOp();
                Value rhs = ((JAssignStmt)unit).getRightOp();
//                System.out.println("\tlhs type : " + lhs.getClass().getName());
//                System.out.println("\trhs type : " + rhs.getClass().getName());
                if (lhs instanceof JInstanceFieldRef) {
                    generateLhsFieldCounters(lhs, unit, counterClass, classToReadMethods, 
                        classToWriteMethods, insertionPairs);
                }
                else if (lhs instanceof JArrayRef) {
                    generateLhsArrayCounters(lhs, unit, counterClass, classToReadMethods, 
                        classToWriteMethods, insertionPairs);

                }
                if (rhs instanceof JInstanceFieldRef) {
                    generateRhsFieldCounters(rhs, unit, counterClass, classToReadMethods, 
                        classToWriteMethods, insertionPairs);
                }
                else if (rhs instanceof JArrayRef) {
                    generateRhsArrayCounters(rhs, unit, counterClass, classToReadMethods, 
                        classToWriteMethods, insertionPairs);
                }
//                System.out.println("\n--------\n");
            }
        }
        for (InsertionPair<Unit> pair : insertionPairs) {
            units.insertBefore(pair.toInsert, pair.point);
        }
        body.validate();
    }

    static void generateLhsArrayCounters(Value lhs, Unit unit, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods,
                    ArrayList<InsertionPair<Unit>> insertionPairs) {
        String fullClassName = ((JArrayRef)lhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "Array");
        ClassInstrumentationUtil.createCounterMethods(fullClassName, 
            counterClass, classToReadMethods, classToWriteMethods,
            generatedFunctionNames);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToWriteMethods, unit)
        );
        String typeName = ((JArrayRef)lhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "");
        if (isPrimitive(typeName)) {
            ClassInstrumentationUtil.createCounterMethods(typeName, 
                counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
            insertionPairs.add(
                generateInsertionPair(typeName, classToWriteMethods, unit)
            );
        }
    }

    static void generateRhsArrayCounters(Value rhs, Unit unit, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods,
                    ArrayList<InsertionPair<Unit>> insertionPairs) {
        String fullClassName = ((JArrayRef)rhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "Array");
        ClassInstrumentationUtil.createCounterMethods(fullClassName,
            counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToReadMethods, unit)
        );
        String typeName = ((JArrayRef)rhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "");
        if (isPrimitive(typeName)) {
            ClassInstrumentationUtil.createCounterMethods(typeName, 
                counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
            insertionPairs.add(
                generateInsertionPair(typeName, classToReadMethods, unit)
            );
        }
    }

    // Generate counter code for the lhs in an assignment statement
    static void generateLhsFieldCounters(Value lhs, Unit unit, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods,
                    ArrayList<InsertionPair<Unit>> insertionPairs) {
        String fullClassName = findClassName((JInstanceFieldRef)lhs);
        ClassInstrumentationUtil.createCounterMethods(fullClassName,
            counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToWriteMethods, unit)
        );
        String typeName = findTypeName((JInstanceFieldRef)lhs);
        if (isPrimitive(typeName)) {
            ClassInstrumentationUtil.createCounterMethods(typeName, 
                counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
            insertionPairs.add(
                generateInsertionPair(typeName, classToWriteMethods, unit)
            );
        }
    }

    // Generate counter code for the rhs in an assignment statement
    static void generateRhsFieldCounters(Value rhs, Unit unit, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods,
                    ArrayList<InsertionPair<Unit>> insertionPairs) {

        String fullClassName = findClassName((JInstanceFieldRef)rhs);
        ClassInstrumentationUtil.createCounterMethods(fullClassName,
            counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToReadMethods, unit)
        );
        String typeName = findTypeName((JInstanceFieldRef)rhs);
        if (isPrimitive(typeName)) {
            ClassInstrumentationUtil.createCounterMethods(typeName, 
                counterClass, classToReadMethods, classToWriteMethods, generatedFunctionNames);
            insertionPairs.add(
                generateInsertionPair(typeName, classToReadMethods, unit)
            );
        }

    }
    static InsertionPair generateInsertionPair(String fullClassName, HashMap<String, SootMethod> classToMethods, Unit unit) {
        SootMethod method = classToMethods.get(fullClassName);
        Unit call = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(method.makeRef()));
        InsertionPair<Unit> pair = new InsertionPair<Unit>(call, unit);
        return pair;
    }

   

    static String findFullMethodName(SootMethod method) {
        String name = method.getName();
        name = name.replace("<", "");
        name = name.replace(">", "");
        return method.getDeclaringClass().getName() + "_" + name;
    }

    // The following code is for tracking FUNCTIONS 
    static class FunctionTracker extends BodyTransformer {

        SootClass counterClass;
        HashSet<String> counterMethodNames = new HashSet<String>();
        HashMap<String,SootMethod> functionNamesToMethods = new HashMap<String, SootMethod>();
        public FunctionTracker(SootClass counterClass) {
            this.counterClass = counterClass;
        }

        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if(AndroidUtil.isAndroidMethod(b.getMethod()) || generatedFunctionNames.contains(b.getMethod().getName())) {
                return;
            }
            JimpleBody body = (JimpleBody) b;
            UnitPatchingChain units = b.getUnits();
            String fullMethodString = findFullMethodName(b.getMethod());
            if (this.counterMethodNames.contains(fullMethodString)) {
                return;
            }
            this.counterMethodNames.add(fullMethodString);
            SootMethod counterMethod = ClassInstrumentationUtil
                .generateFunctionCounter(fullMethodString, this.counterClass, generatedFunctionNames);
            Unit call = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(counterMethod.makeRef()));
            // Insert the generated statement before the first  non-identity stmt
            units.insertBefore(call, body.getFirstNonIdentityStmt());
            // Validate the body to ensure that our code injection does not introduce any problem (at least statically)
            b.validate();
        }
    } 
}

class InsertionPair<E> {
    protected final E toInsert;
    protected final E point;
    public InsertionPair(E toInsert, E point) {
        this.toInsert = toInsert;
        this.point = point; 
    }
}

class ObjectProfilingData {
    protected final SootField staticCounter;
    protected final SootField serialField;
    protected final SootField readsField;
    protected final SootField writesField;

    public ObjectProfilingData(SootField staticCounter, SootField serialField, SootField readsField, SootField writesField) {
        this.staticCounter = staticCounter;
        this.serialField = serialField; 
        this.readsField = readsField;
        this.writesField = writesField;
    }
}
