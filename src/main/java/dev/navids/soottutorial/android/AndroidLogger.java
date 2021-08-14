
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
    private static String androidJar = USER_HOME + "/Documents/android/platforms";
    private static HashSet<String> generatedFunctionNames = new HashSet<String>();
    static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator + "Android";
    static String apkPath = androidDemoPath + File.separator + "/brilliant.apk";
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
        Iterator<SootClass> classIt = Scene.v().getApplicationClasses().iterator();
        HashMap<SootMethod, ObjectProfilingData> constructorsToData = new HashMap<>();
        while (classIt.hasNext()) {
            SootClass currentClass = classIt.next();
            if (currentClass.getName().equals(counterClass.getName()) || currentClass.isInterface()) {
                continue;
            }
            System.out.println("Class : " + currentClass.getName());
            List<SootMethod> methods = currentClass.getMethods();
            addObjectAccessFields(currentClass, counterClass, classNamesToObjectData, 
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
        HashMap <String, SootClass> arrayClasses;
        SootClass counterClass;
        String packageName;
        public ObjectLoggingInjector(SootClass counterClass, HashMap<String,SootMethod> classNamesToReadIncrementors,
               HashMap<String,SootMethod> classNamesToWriteIncrementors, String packageName) {
            this.counterClass = counterClass;
            this.classNamesToReadIncrementors = classNamesToReadIncrementors;
            this.classNamesToWriteIncrementors = classNamesToWriteIncrementors;
            this.classNamesToObjectData = new HashMap<>();
            this.arrayClasses = new HashMap<>();
            this.packageName = packageName;
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
            ArrayList<InsertionPair<Unit>> insertionPairs = new ArrayList<InsertionPair<Unit>>();
            while (it.hasNext()) {
                Unit unit = it.next();
                if (unit instanceof JAssignStmt) {
                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (lhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)lhs, 
                            insertionPairs, classNamesToWriteIncrementors, unit); 
                    }
                    else if (lhs instanceof JNewArrayExpr) {
                        createArrayClass((JNewArrayExpr)lhs, insertionPairs);
                    }

                    if (rhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)rhs, 
                            insertionPairs, classNamesToReadIncrementors, unit);
                    }
                    else if (rhs instanceof JNewArrayExpr) {
                        createArrayClass((JNewArrayExpr)rhs, insertionPairs);
                    }
                }
            }
            for (InsertionPair<Unit> pair : insertionPairs) {
                units.insertBefore(pair.toInsert, pair.point);
            }
            body.validate();
            lock.unlock();
        }

        public SootMethod createArrayConstructor(SootClass arrayClass, String arrayClassName, Type arrayType, SootField counterField) {

            String methodName = "<init>";
            SootMethod constructor = new SootMethod(methodName,
                Arrays.asList(new Type[]{arrayType}),
                VoidType.v(), Modifier.PUBLIC);
            arrayClass.addMethod(constructor);
            JimpleBody body = Jimple.v().newBody(constructor);
            UnitPatchingChain units = body.getUnits();

            Value thisRef = Jimple.v().newThisRef(arrayClass.getType());

            Local thisLocal = InstrumentUtil.generateNewLocal(body, arrayClass.getType());
            units.add(Jimple.v().newIdentityStmt(thisLocal, thisRef));
            Local paramLocal = InstrumentUtil.generateNewLocal(body, arrayType);
            ParameterRef arrayParam = Jimple.v().newParameterRef(arrayType, 0);
            units.add(Jimple.v().newIdentityStmt(paramLocal, arrayParam));
            InstanceFieldRef arrayFieldRef = Jimple.v().newInstanceFieldRef(thisLocal, 
                arrayClass.getFieldByName("array").makeRef());
            units.add(Jimple.v().newAssignStmt(arrayFieldRef, paramLocal));

            Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
            units.add(Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(counterField.makeRef())));
            units.add(Jimple.v().newAssignStmt(counterLocal, 
                    Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));
            units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counterField.makeRef()), counterLocal));

            units.addAll(InstrumentUtil.generateLogStmts(body, arrayClass.getName() + " intiailized id = ", counterLocal));


            Unit returnUnit = Jimple.v().newReturnVoidStmt();
            units.add(returnUnit);

            System.out.println("NEW CONSTRUCTOR:\n" + body.toString());
            body.validate();
            constructor.setActiveBody(body);


            return constructor;
        }

        public SootClass createArrayClass(JNewArrayExpr arrayExpr, List<InsertionPair<Unit>> insertionPairs) {
            Type arrayType = arrayExpr.getType();
            String arrayClassName = arrayType
                .toString()
                .replace(".", "")
                .replace("[", "")
                .replace("]", "") + "Array";

            if (this.arrayClasses.containsKey(arrayClassName)) {
                return null;
            }
            String signature = this.packageName + "." + arrayClassName;
            SootClass arrayClass = new SootClass(signature, Modifier.PUBLIC);
            arrayClass.setSuperclass(Scene.v().getSootClass("java.lang.Object")); 
            arrayClass.setApplicationClass();

            HashMap <String, ObjectProfilingData> classNamesToObjectData = new HashMap<>();
            HashMap <String, SootMethod> classNamesToReadIncrementors = new HashMap<>();
            HashMap <String, SootMethod> classNamesToWriteIncrementors = new HashMap<>();
            addObjectAccessFields(arrayClass, this.counterClass, classNamesToObjectData, 
                  classNamesToReadIncrementors, classNamesToWriteIncrementors);
            SootField array = new SootField("array", arrayType);
            arrayClass.addField(array);
            System.out.println("Created class " + signature);
            ObjectProfilingData data = classNamesToObjectData.get(arrayClass.getName());
            SootMethod constructor = createArrayConstructor(arrayClass, arrayClassName, arrayType, data.staticCounter); 
            this.arrayClasses.put(arrayClassName, arrayClass);
            return arrayClass; 
        }

        public void invokeObjectMethods(JInstanceFieldRef fieldRef, 
            ArrayList<InsertionPair<Unit>> insertionPairs, 
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
            insertionPairs.add(new InsertionPair<Unit>(call, unit));
        }
    }

    static void addObjectAccessFields(SootClass currentClass, SootClass counterClass, HashMap <String, ObjectProfilingData> classNamesToObjectData, 
        HashMap <String, SootMethod> classNamesToReadIncrementors, HashMap <String, SootMethod> classNamesToWriteIncrementors) {
        String [] strArray = currentClass.getName().split("\\.");
        String className = strArray[strArray.length - 1];
        String joinedClassName = String.join("", strArray);
        SootField staticCounter = addStaticCounter(joinedClassName, counterClass);
        SootField serialField = addClassField("serial", currentClass);
        SootField readsField = addClassField("reads", currentClass);
        SootField writesField = addClassField("writes", currentClass);
        classNamesToObjectData.put(currentClass.getName(), 
            new ObjectProfilingData(staticCounter, serialField, readsField, writesField));

        classNamesToReadIncrementors.put(joinedClassName,
            createIncrementor(currentClass, "incReads", readsField, currentClass.getName() + " object reads = "));
        classNamesToWriteIncrementors.put(joinedClassName, 
            createIncrementor(currentClass, "incWrites", writesField, currentClass.getName() + " object writes = "));

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

    static SootMethod createIncrementor(SootClass currentClass, String name, SootField currentField, String logMessage) {
        String methodName = name;
        if (currentClass.declaresMethodByName(methodName)) {
            return currentClass.getMethodByName(methodName);
        }
        SootMethod getter = new SootMethod(methodName,
            Arrays.asList(new Type[]{}),
            VoidType.v(), Modifier.PUBLIC);
        currentClass.addMethod(getter);
        JimpleBody body = Jimple.v().newBody(getter);
        UnitPatchingChain units = body.getUnits();

        ThisRef thisRef = Jimple.v().newThisRef(currentClass.getType());
        Local base = InstrumentUtil.generateNewLocal(body, currentClass.getType());
        IdentityStmt idStmt = Jimple.v().newIdentityStmt(base, thisRef);
        units.add(idStmt);
        InstanceFieldRef instanceFieldRef = Jimple.v().newInstanceFieldRef(base, currentField.makeRef());
        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(counterLocal, instanceFieldRef));
        units.add(Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));

        InstanceFieldRef instanceFieldRef2 = Jimple.v().newInstanceFieldRef(base, currentField.makeRef());
        units.add(Jimple.v().newAssignStmt(instanceFieldRef2, counterLocal));

        // Get serial value for log
        SootField serialField = currentClass.getFieldByName("serial");
        InstanceFieldRef serialFieldRef = Jimple.v().newInstanceFieldRef(base, serialField.makeRef());
        Local serialLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(serialLocal, serialFieldRef));
        units.addAll(InstrumentUtil.generateLogStmts(body, currentClass.getName() + " serial id = ", serialLocal));

        // Log for reads/writes count
        units.addAll(InstrumentUtil.generateLogStmts(body, logMessage, counterLocal));
        units.add(Jimple.v().newReturnVoidStmt());
        body.validate();
        getter.setActiveBody(body);
        return getter;
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
        generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToWriteMethods, unit)
        );
        String typeName = ((JArrayRef)lhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "");
        if (isPrimitive(typeName)) {
            generateMethods(typeName, counterClass, classToReadMethods, classToWriteMethods);
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
        generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToReadMethods, unit)
        );
        String typeName = ((JArrayRef)rhs)
                .getBase()
                .getType()
                .toString()
                .replace("[]", "");
        if (isPrimitive(typeName)) {
            generateMethods(typeName, counterClass, classToReadMethods, classToWriteMethods);
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
        generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToWriteMethods, unit)
        );
        String typeName = findTypeName((JInstanceFieldRef)lhs);
        if (isPrimitive(typeName)) {
            generateMethods(typeName, counterClass, classToReadMethods, classToWriteMethods);
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
        generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
        insertionPairs.add(
            generateInsertionPair(fullClassName, classToReadMethods, unit)
        );
        String typeName = findTypeName((JInstanceFieldRef)rhs);
        if (isPrimitive(typeName)) {
            generateMethods(typeName, counterClass, classToReadMethods, classToWriteMethods);
            insertionPairs.add(
                generateInsertionPair(typeName, classToReadMethods, unit)
            );
        }

    }
    static void generateMethods(String fullClassName, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods) {
        if (!classToReadMethods.containsKey(fullClassName)) {
            SootMethod incReadMethod = generateReadCounter(fullClassName, counterClass);
            SootMethod incWriteMethod = generateWriteCounter(fullClassName, counterClass);
            classToReadMethods.put(fullClassName, incReadMethod);
            classToWriteMethods.put(fullClassName, incWriteMethod);
        }
    }

    static InsertionPair generateInsertionPair(String fullClassName, HashMap<String, SootMethod> classToMethods, Unit unit) {
        SootMethod method = classToMethods.get(fullClassName);
        Unit call = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(method.makeRef()));
        InsertionPair<Unit> pair = new InsertionPair<Unit>(call, unit);
        return pair;
    }

    static SootMethod generateReadCounter(String fullClassName, SootClass counterClass) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField readCounter = addStaticCounter(joinedName + "Read", counterClass);
        SootMethod readIncMethod = createMethod(counterClass,  
            joinedName + "Read", fullClassName + " read", readCounter);
        return readIncMethod;
    }

    static SootMethod generateWriteCounter(String fullClassName, SootClass counterClass) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField writeCounter = addStaticCounter(joinedName + "Write", counterClass);
        SootMethod writeIncMethod = createMethod(counterClass, 
            joinedName + "Write", fullClassName + " write", writeCounter);
        return writeIncMethod;
    }
    static SootMethod generateFunctionCounter(String fullFunctionName, SootClass counterClass) {
        String [] strArray = fullFunctionName.split("\\.");
        String functionName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField functionCounter = addStaticCounter(joinedName + "Call", counterClass);
        SootMethod functionIncMethod = createMethod(counterClass, 
            joinedName + "Call", fullFunctionName + " function call", functionCounter);
        return functionIncMethod;
    }

    // Create new counter for every new object type encountered
    static SootField addStaticCounter(String name, SootClass counterClass) {
        if (!counterClass.declaresFieldByName(name + "Counter")) {
            SootField counterField = new SootField(name + "Counter", 
                IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
            counterClass.addField(counterField);
            return counterField;
        }
        return counterClass.getFieldByName(name + "Counter");
    }
    
    // Field to denote unique id for an object
    static SootField addClassField(String name, SootClass currentClass) {
        if (!currentClass.declaresFieldByName(name)) {
            SootField serialField = new SootField(name,
                IntType.v());
            currentClass.addField(serialField);
            return serialField;
        }
        return currentClass.getFieldByName(name);
    }

    static SootMethod createMethod(SootClass counterClass, String name, String nameForLog, SootField counterField) {
        String methodName = "increment" + name;
        SootMethod incMethod = new SootMethod(methodName,
            Arrays.asList(new Type[]{}),
            VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        generatedFunctionNames.add(methodName);
        counterClass.addMethod(incMethod);
        JimpleBody body = Jimple.v().newBody(incMethod);
        UnitPatchingChain units = body.getUnits();
        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(counterField.makeRef())));
        units.add(Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));
        units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counterField.makeRef()), counterLocal));
        units.addAll(InstrumentUtil.generateLogStmts(body, nameForLog + " counter = ", counterLocal));
        Unit returnUnit = Jimple.v().newReturnVoidStmt();
        units.add(returnUnit);
        body.validate();
        incMethod.setActiveBody(body);
        return incMethod;
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
            SootMethod counterMethod = generateFunctionCounter(fullMethodString, this.counterClass);
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
