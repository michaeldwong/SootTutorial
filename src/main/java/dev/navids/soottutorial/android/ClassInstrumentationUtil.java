package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class ClassInstrumentationUtil {
    static void addObjectAccessFields(SootClass currentClass, SootClass counterClass, String name, HashMap <String, ObjectProfilingData> classNamesToObjectData, 
        HashMap <String, SootMethod> classNamesToReadIncrementors, HashMap <String, SootMethod> classNamesToWriteIncrementors) {
        String [] strArray = currentClass.getName().split("\\.");
        String className = strArray[strArray.length - 1];
        String joinedClassName = String.join("", strArray);
        SootField staticCounter = addStaticCounter(joinedClassName, counterClass);
        SootField serialField = addClassField("serial", currentClass);
        SootField readsField = addClassField("reads", currentClass);
        SootField writesField = addClassField("writes", currentClass);
        classNamesToObjectData.put(name, 
            new ObjectProfilingData(staticCounter, serialField, readsField, writesField));

        classNamesToReadIncrementors.put(name,
            createIncrementor(currentClass, "incReads", readsField, currentClass.getName() + " object reads = "));
        classNamesToWriteIncrementors.put(name, 
            createIncrementor(currentClass, "incWrites", writesField, currentClass.getName() + " object writes = "));

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


    static void createCounterMethods(String fullClassName, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods,
                    HashSet<String> generatedFunctionNames) {
        if (!classToReadMethods.containsKey(fullClassName)) {
            SootMethod incReadMethod = generateReadCounter(fullClassName, counterClass, generatedFunctionNames);
            SootMethod incWriteMethod = generateWriteCounter(fullClassName, counterClass, generatedFunctionNames);
            classToReadMethods.put(fullClassName, incReadMethod);
            classToWriteMethods.put(fullClassName, incWriteMethod);
        }
    }


    static SootMethod generateReadCounter(String fullClassName, 
        SootClass counterClass, HashSet<String> generatedFunctionNames) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField readCounter = addStaticCounter(joinedName + "Read", counterClass);
        SootMethod readIncMethod = createCounterMethod(counterClass,  
            joinedName + "Read", fullClassName + " read", readCounter, generatedFunctionNames);
        return readIncMethod;
    }

    static SootMethod generateWriteCounter(String fullClassName, SootClass counterClass, 
           HashSet<String>generatedFunctionNames) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField writeCounter = addStaticCounter(joinedName + "Write", counterClass);
        SootMethod writeIncMethod = createCounterMethod(counterClass, 
            joinedName + "Write", fullClassName + " write", writeCounter, generatedFunctionNames);
        return writeIncMethod;
    }
    static SootMethod generateFunctionCounter(String fullFunctionName, 
            SootClass counterClass, HashSet<String> generatedFunctionNames) {
        String [] strArray = fullFunctionName.split("\\.");
        String functionName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField functionCounter = addStaticCounter(joinedName + "Call", counterClass);
        SootMethod functionIncMethod = createCounterMethod(counterClass, 
            joinedName + "Call", fullFunctionName + " function call", functionCounter, generatedFunctionNames);
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

    static SootMethod createCounterMethod(SootClass counterClass, String name, 
           String nameForLog, SootField counterField, HashSet<String> generatedFunctionNames) {
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
    static boolean isArrayType(Type type) {
        return type.toString().contains("[]");
    }
    static String typeToWrapperName(Type elementType) {
        String [] strArray = elementType.toString().split("\\.");
        String lastElement = strArray[strArray.length - 1];
        if (ClassInstrumentationUtil.isArrayType(elementType)) {
            return lastElement.replace("[]", "Array");
        }
        return lastElement;
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


}
