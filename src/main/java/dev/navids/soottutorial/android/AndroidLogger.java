
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
//    private static String androidJar = USER_HOME + "/Documents/android/platforms";
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
        instrumentClasses(counterClass, classNamesToReadIncrementors, classNamesToWriteIncrementors, classNamesToObjectData);
        PackManager.v().getPack("jtp").add(
            new Transform("jtp.recordAccesses", 
                new ObjectLoggingInjector(counterClass, classNamesToReadIncrementors, classNamesToWriteIncrementors, packageName)
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
            addSerialInitialization(body, 
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

    static class ObjectLoggingInjector extends BodyTransformer {

        HashMap <String, SootMethod> classNamesToReadIncrementors;
        HashMap <String, SootMethod> classNamesToWriteIncrementors;
        HashMap <String, ObjectProfilingData> classNamesToObjectData;
        SootClass counterClass;
        String packageName;
        ArrayWrapperCreator arrayWrapperCreator;
        public ObjectLoggingInjector(SootClass counterClass, HashMap<String,SootMethod> classNamesToReadIncrementors,
               HashMap<String,SootMethod> classNamesToWriteIncrementors, String packageName) {
            this.counterClass = counterClass;
            this.classNamesToReadIncrementors = classNamesToReadIncrementors;
            this.classNamesToWriteIncrementors = classNamesToWriteIncrementors;
            this.classNamesToObjectData = new HashMap<>();
            this.packageName = packageName;
            this.arrayWrapperCreator = new ArrayWrapperCreator(counterClass, packageName);
        }

        public String typeToWrapperName(Type elementType) {
            String [] strArray = elementType.toString().split("\\.");
            String lastElement = strArray[strArray.length - 1];
            if (isArrayType(elementType)) {
                return lastElement.replace("[]", "Array");
            }
            return lastElement;
        }
        private boolean isArrayType(Type type) {
            return type.toString().contains("[]");
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
            HashMap <String,SootClass> namesToArrayClasses = new HashMap<>();
            ArrayList<InsertionPair<Unit>> beforePairs = new ArrayList<InsertionPair<Unit>>();
            ArrayList<InsertionPair<Unit>> swapPairs = new ArrayList<InsertionPair<Unit>>();
            changeMethodParameterTypes(b.getMethod(), namesToArrayClasses);

            // TODO: Move cahngeMethodtypes and paramref updates to another function 
            // pass over classes. Then, once method signatures ahve been changed, 
            // Make the pass to the object access methods
            System.out.println("ORIGINAL: " + body.toString());
            while (it.hasNext()) {
                Unit unit = it.next();
                if (unit instanceof JIdentityStmt) {
                    Value rhs = ((JIdentityStmt)unit).getRightOp();
                    Value lhs = ((JIdentityStmt)unit).getLeftOp();
                    if (rhs instanceof ParameterRef) {
                        Type t = rhs.getType();
                        if (isArrayType(t)) {
                            Type elementType = ((ArrayType)t).getElementType();
                            String wrapperName = typeToWrapperName(elementType);
                            if (!namesToArrayClasses.containsKey(wrapperName)) {
                                System.out.println(wrapperName + " NOT included for paramref updates");
                            }
                            SootClass wrapper = namesToArrayClasses.get(wrapperName);
                            ParameterRef newParamRef = Jimple.v().newParameterRef(
                                wrapper.getType(),
                                ((ParameterRef)rhs).getIndex()
                            );
                            ((JimpleLocal)lhs).setType(wrapper.getType());
                            ((JIdentityStmt)unit).setRightOp(newParamRef);
                        }
                    }
                }
                if (unit instanceof JAssignStmt) {
                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (lhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)lhs, 
                            beforePairs, this.classNamesToWriteIncrementors, unit); 
                    }
                    else if (lhs instanceof JNewArrayExpr) {
                    }
                    else if (lhs instanceof JArrayRef) {
                        arrayRefWrite(unit, lhs, rhs, namesToArrayClasses, beforePairs, swapPairs);
                    }
                    if (rhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)rhs, 
                            beforePairs, this.classNamesToReadIncrementors, unit);
                    }
                    else if (rhs instanceof JNewArrayExpr) {
                        replaceNewArray(unit, lhs, rhs, namesToArrayClasses, beforePairs, swapPairs);
                    }
                    else if (rhs instanceof JArrayRef) {

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
                if (unit instanceof JAssignStmt) {
                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (isArrayType(lhs.getType())) {
                        System.out.println(unit.toString());
                        System.out.println("\tlhs is array : " + lhs.toString() + " and is type " + lhs.getClass().getName());
                        System.out.println("\trhs : " + rhs.toString() + " is type " + rhs.getClass().getName());
                        String wrapperName = typeToWrapperName(rhs.getType());
                        SootClass wrapper;
                        System.out.println("Current wrapperName = " + wrapperName);
                        if (namesToArrayClasses.containsKey(wrapperName)) {
                            wrapper = namesToArrayClasses.get(wrapperName);
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
                    
//                    InstanceFieldRef arrayField = Jimple.v().newInstanceFieldRef(rhs, 
//                        arrayClass.getFieldByName("array").makeRef());

//                       lhs.setType(rhs.getType());
                    }
                    if (isArrayType(rhs.getType())) {
                        System.out.println(unit.toString());
                        System.out.println("\trhs is array : " + rhs.toString() + " and is type " + rhs.getClass().getName());
                        System.out.println("\tlhs : " + lhs.toString() + " is type " + lhs.getClass().getName());

                   }
                }
            }
            for (InsertionPair<Unit> pair : beforePairs) {
                units.insertBefore(pair.toInsert, pair.point);
            }
            for (InsertionPair<Unit> pair : swapPairs) {
                units.swapWith(pair.point, pair.toInsert);
            }


            System.out.println("Current class: " + b.getMethod().getDeclaringClass().getName());
            System.out.println("Validating:\n" + body.toString());
            body.validate();
            lock.unlock();
        }

        private void changeMethodParameterTypes(SootMethod method, HashMap <String,SootClass> namesToArrayClasses) {
            boolean changed = false;
            List <Type> paramTypes = method.getParameterTypes();
            for (int i = 0; i < paramTypes.size(); i++) {
                Type t = paramTypes.get(i);
                if (isArrayType(t)) {
                    Type elementType = ((ArrayType)t).getElementType();
                    String wrapperName = typeToWrapperName(elementType);
                    System.out.println("Changing type " + t.toString() + " to " + wrapperName);
                    SootClass wrapper;
                    if (!namesToArrayClasses.containsKey(wrapperName)) {
                        System.out.println("wrapperName not present for method param change");
                        wrapper = this.arrayWrapperCreator.createArrayClass(elementType, 
                            this.classNamesToReadIncrementors, this.classNamesToWriteIncrementors);
                        namesToArrayClasses.put(wrapperName, wrapper);

                    }
                    else {
                        wrapper = namesToArrayClasses.get(wrapperName);
                    }
                    Type newType = wrapper.getType(); 
                    paramTypes.set(i, newType);
                    changed = true;
                }
            }
            if (changed) {
                method.setParameterTypes(paramTypes);
                System.out.println("Changed : " + method.toString());
            }
        }

        private void arrayRefWrite(Unit unit, Value lhs, Value rhs, HashMap <String,SootClass>namesToArrayClasses, 
                        ArrayList<InsertionPair<Unit>>beforePairs, ArrayList<InsertionPair<Unit>>swapPairs) {
            Type elementType = ((ArrayRef)lhs).getType();
            if (elementType.toString().contains("[]")) {
                // For now skip multidimensional arrays
                // TODO: Complete
                System.out.println("\tSkipping " + elementType);
                return;
            }
            String wrapperName = typeToWrapperName(elementType);
            SootClass wrapper;
            if (namesToArrayClasses.containsKey(wrapperName)) {
                wrapper = namesToArrayClasses.get(wrapperName);
            }
            else {
                wrapperName = this.arrayWrapperCreator.arrayTypeToName(elementType);
                wrapper = this.arrayWrapperCreator.createArrayClass(elementType, 
                    this.classNamesToReadIncrementors, this.classNamesToWriteIncrementors);
                System.out.println("Creating wrapper for " + wrapperName);
                namesToArrayClasses.put(wrapperName, wrapper); 
            }
            Value lhsLocal = ((JArrayRef)lhs).getBase();
            ((Local)lhsLocal).setType(wrapper.getType());
            SootMethod setMethod = wrapper.getMethodByName("set");
            Unit call = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr((Local)lhsLocal, 
                setMethod.makeRef(), ((JArrayRef)lhs).getIndex(), rhs));
            swapPairs.add(new InsertionPair<Unit>(call, unit));
        }

        private void replaceNewArray(Unit unit, Value lhs, Value rhs, HashMap <String,SootClass>namesToArrayClasses, 
                        ArrayList<InsertionPair<Unit>>beforePairs, ArrayList<InsertionPair<Unit>>swapPairs) {
            Type elementType = ((JNewArrayExpr)rhs).getBaseType();
            Value size = ((JNewArrayExpr)rhs).getSize();
            if (elementType.toString().contains("[]")) {
                // For now skip multidimensional arrays
                // TODO: Complete
                System.out.println("\tSkipping " + elementType);
                return;
            }
            String wrapperName = typeToWrapperName(elementType);
            SootClass wrapper;
            if (namesToArrayClasses.containsKey(wrapperName)) {
                wrapper = namesToArrayClasses.get(wrapperName);
            }
            else {
                wrapperName = this.arrayWrapperCreator.arrayTypeToName(elementType);
                wrapper = this.arrayWrapperCreator.createArrayClass(elementType, 
                    this.classNamesToReadIncrementors, this.classNamesToWriteIncrementors);
                namesToArrayClasses.put(wrapperName, wrapper);
                System.out.println("Creating wrapper for " + wrapperName);
            }
            namesToArrayClasses.put(wrapperName, wrapper);
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
            System.out.println(currentClass.getName() + " found ");
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
    }


    static void addSerialInitialization(JimpleBody body, SootField serialField, SootField staticCounterField, SootClass currentClass) {
        UnitPatchingChain units = body.getUnits();
        Iterator<Unit> it = units.iterator();
        Value thisRefLocal = null;
        while (it.hasNext()) {
            Unit unit = it.next();
            if (unit instanceof JIdentityStmt) {
                Value rightOp = ((JIdentityStmt)unit).getRightOp();
                if (rightOp instanceof ThisRef) {
                    thisRefLocal = ((JIdentityStmt)unit).getLeftOp();
                }
            }
        }
        if (thisRefLocal == null) {
            thisRefLocal = Jimple.v().newThisRef(currentClass.getType());
        }
        InstanceFieldRef serialFieldRef = Jimple.v().newInstanceFieldRef(thisRefLocal, serialField.makeRef());
        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        Unit u1 = Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(staticCounterField.makeRef()));
        Unit u2 = Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1)));
        Unit u3 = Jimple.v().newAssignStmt(serialFieldRef, counterLocal);
        Unit u4 = Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(staticCounterField.makeRef()), counterLocal);

        units.insertBefore(InstrumentUtil.generateLogStmts(body, currentClass.getName() + " intiailized id = ", 
            counterLocal), body.getFirstNonIdentityStmt());
        units.insertBefore(u4, body.getFirstNonIdentityStmt());
        units.insertBefore(u3, body.getFirstNonIdentityStmt());
        units.insertBefore(u2, body.getFirstNonIdentityStmt());
        units.insertBefore(u1, body.getFirstNonIdentityStmt());

        body.validate(); 
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
