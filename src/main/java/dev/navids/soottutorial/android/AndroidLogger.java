
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
            ClassInstrumentationUtil.addObjectAccessFields(currentClass, counterClass, classNamesToObjectData, 
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
            ArrayList<InsertionPair<Unit>> afterPairs = new ArrayList<InsertionPair<Unit>>();
            while (it.hasNext()) {
                Unit unit = it.next();
                if (unit instanceof JAssignStmt) {
                    Value lhs = ((JAssignStmt)unit).getLeftOp();
                    Value rhs = ((JAssignStmt)unit).getRightOp();
                    if (lhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)lhs, 
                            beforePairs, classNamesToWriteIncrementors, unit); 
                    }
                    else if (lhs instanceof JNewArrayExpr) {
                        this.arrayWrapperCreator.createArrayClass((JNewArrayExpr)lhs);
                    }

                    if (rhs instanceof JInstanceFieldRef) {
                        invokeObjectMethods((JInstanceFieldRef)rhs, 
                            beforePairs, classNamesToReadIncrementors, unit);
                    }
                    else if (rhs instanceof JNewArrayExpr) {
                        SootClass wrapper = this.arrayWrapperCreator.createArrayClass((JNewArrayExpr)rhs);
                        NewExpr newExpr = Jimple.v().newNewExpr(wrapper.getType());
                        Local wrapperLocal = InstrumentUtil.generateNewLocal(body, wrapper.getType());
                        Unit wrapperAssign = Jimple.v().newAssignStmt(wrapperLocal, newExpr);
                        InsertionPair<Unit>pair = new InsertionPair<Unit>(wrapperAssign, unit);
                        afterPairs.add(pair);
                        // TODO: Need to iterate through methods to get constructor
                        Unit call = Jimple.v().newInvokeStmt((Jimple.v().newSpecialInvokeExpr(wrapperLocal, 
                            wrapper.getMethodByName("<init>").makeRef(), lhs)));
                        afterPairs.add(new InsertionPair<Unit>(call, wrapperAssign));
                    }
                }
            }
            for (InsertionPair<Unit> pair : beforePairs) {
                units.insertBefore(pair.toInsert, pair.point);
            }
            for (InsertionPair<Unit> pair : afterPairs) {
                units.insertAfter(pair.toInsert, pair.point);
            }
            System.out.println("Current class: " + b.getMethod().getDeclaringClass().getName());
            System.out.println("Validating:\n" + body.toString());
            body.validate();
            lock.unlock();
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
