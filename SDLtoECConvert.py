import sdlpath
from sdlparser.SDLParser import *
import re, importlib

initFuncName_EC = "Init"
dummyVarInMain_EC = "dummy"
vVarInMain_EC = "v"
additionOperator_EC = "+"
intType_EC = "int"
countVarPrefix = "count_"
advPubKeyVarName_EC = "adv_public_key"
adversaryVarName_EC = "Adv"
adversaryKeyword_EC = "adversary"
funcNamesAdvDoesntNeed = ["types", "count", "precompute", "NONE_FUNC_NAME"]
sVarInMain_EC = "s"
messageVarNameInMain_EC = "m"
emptyMapSymbol_EC = "[]"
emptyMapName_EC = "empty_map"
randomOracleVarName_EC = "rand_oracle"
randomG1GenerationStmt_EC = "Rand_G_1()"
randomZRGenerationStmt_EC = "Rand_Z_R()"
funcName_EC = "fun"
trueKeyword_EC = "true"
trueKeyword_SDL = "True"
falseKeyword_SDL = "False"
numSpacesForIndent = 2
templateFileName = "ECTemplate.txt"
#configFileName = "SDLtoECConfig"
booleanType_EC = "bool"
varKeyword_EC = "var"
abstractKeyword_EC = "abs"
adversaryIdentifier_EC = "A"
adversarySignatureIdentifier_EC = "Adv"
hashFuncName_EC = "Hash"
signFuncName_EC = "Sign"
verifyFuncName_EC = "Verify"
messageName_EC = "m"
messageType_EC = "message"
secretKeyName_EC = "secret_key"
queriedName_EC = "queried"
varNameForVerifyBoolRetVal_EC = "v"
appendOperator_EC = "::"
funcStartChar_EC = "{"
funcEndChar_EC = "}"
assignmentOperator_EC = "="
returnKeyword_EC = "return"
multOp_EC = "*"
expOp_EC = "^"
endOfLineOperator_EC = ";"
eqTstOperator_EC = "="
validGroupTypes = ["G1", "G2", "GT", "ZR"]
validHashGroupTypes = ["G1", "G2", "ZR"]
validRandomGroupTypes = ["G1", "G2", "ZR"]

DEBUG = False

def writeNumOfSpacesToString(numSpaces):
    outputString = ""

    for space in range(0, numSpaces):
        outputString += " "

    return outputString

def addTemplateLinesToOutputECFile(outputECFile):
    templateFile = open(templateFileName, 'r')
    outputString = ""

    for templateLine in templateFile:
        outputString += templateLine

    outputECFile.write(outputString)

def removeChars(inputString, inputChars):
    inputStringSplit = inputString.split(inputChars)
    outputString = ""
    for inputStringSplitInd in inputStringSplit:
        outputString += inputStringSplitInd

    return outputString

def getSchemeName(SDLFileName):
    SDLFileNameSplit = SDLFileName.split("/")
    lenSplit = len(SDLFileNameSplit)
    SDLFileName = SDLFileNameSplit[(lenSplit - 1)]

    SDLFileName = SDLFileName.split(".")[0]
    SDLFileName = removeChars(SDLFileName, "-")
    return SDLFileName

def addGameDeclLine(SDLFileName, outputECFile):
    schemeName = getSchemeName(SDLFileName)

    outputString = "game "
    outputString += schemeName
    outputString += "_EF " + assignmentOperator_EC + " " + funcStartChar_EC + "\n"

    outputECFile.write(outputString)

def getAtLeastOneHashCallOrNot(inputSDLFile):
    atLeastOneHashCall = False

    for inputSDLLine in inputSDLFile:
        inputSDLLine = inputSDLLine.lstrip().rstrip()
        if (inputSDLLine.startswith("#") == True):
            continue

        splitLine = inputSDLLine.split(":=")

        # if it's not an assignment node, then there won't be any hash calls
        if (len(splitLine) == 1):
            continue

        if (len(splitLine) > 2):
            sys.exit("getAtLeastOneHashCallOrNot in SDLtoECConvert.py:  line in input SDL file contains more than one := symbols; not allowed in SDL.")

        rightSide = splitLine[1]
        rightSide = rightSide.lstrip().rstrip()
        if (rightSide.startswith("H(") == True):
            return True

        reResult = re.search('[^a-zA-Z0-9_]H\(', rightSide)
        if (reResult != None):
            return True

    return False

def getVarDeps(assignInfo, config, varName, funcName):
    # NOTE:  this function gets variable dependencies in a very specific way.  If the variable name passed
    # in is comprised of a list, all of the members of that list are returned.  Otherwise, the variable
    # name passed in is returned.  Example:
    #
    # pk := list{g, x}
    # would return [g, x]
    #
    # sk := x ^ y
    # would return sk

    if (funcName not in assignInfo):
        sys.exit("getVarDeps in SDLtoECConvert.py:  function name passed in isn't in assignInfo.")

    if (varName not in assignInfo[funcName]):
        sys.exit("getVarDeps in SDLtoECConvert.py:  variable name passed in isn't in the entry of assignInfo for the function name passed in.")

    varDeps = assignInfo[funcName][varName].getListNodesList()
    if (len(varDeps) == 0):
        return [varName]

    return varDeps

def addGlobalVars(outputECFile, assignInfo, config):
    #outputString = "  " + varKeyword_EC + " " + secretKeyName_EC + " : int\n"

    outputString = ""

    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    for secretKeyVar in secretKeyVars:
        currentVarType = getVarTypeFromVarName_EC(secretKeyVar, config.keygenFuncName_SDL)
        outputString += "  " + varKeyword_EC + " " + secretKeyVar + " : " + currentVarType + "\n"

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)

    for publicKeyVar in publicKeyVars:
        currentVarType = getVarTypeFromVarName_EC(publicKeyVar, config.keygenFuncName_SDL)
        outputString += "  " + varKeyword_EC + " " + publicKeyVar + " : " + currentVarType + "\n"

    outputString += "  " + varKeyword_EC + " " + queriedName_EC + " : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  var " + randomOracleVarName_EC + " : (message, G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile, assignInfo, config):
    hashGroupTypeOfSigFunc_SDL = getHashGroupTypeOfFunc(config.signFuncName_SDL, assignInfo, config)
    hashGroupTypeOfSigFunc_EC = convertTypeSDLtoEC_Strings(hashGroupTypeOfSigFunc_SDL)

    outputString = "\n  " + funcName_EC + " " + hashFuncName_EC + "(m : message) : "
    outputString += hashGroupTypeOfSigFunc_EC + " = {\n"
    outputECFile.write(outputString)
    writeCountVarIncrement(outputECFile, hashFuncName_EC)
    outputString = ""
    outputString += "    if(!in_dom(m, " + randomOracleVarName_EC + ")) {\n"
    outputString += "      " + randomOracleVarName_EC + "[m] = Rand_G_1();\n"
    outputString += "    }\n"
    outputString += "    return " + randomOracleVarName_EC + "[m];\n"
    outputString += "  }\n\n"

    outputECFile.write(outputString)

def addStatementsForPresenceOfHashes(outputECFile, assignInfo, config):
    addGlobalVarsForHashes(outputECFile)
    addHashFuncDef(outputECFile, assignInfo, config)

def getInputSDLFileMetadata(inputSDLFileName):
    parseFile(inputSDLFileName, False, True)
    assignInfo = getAssignInfo()
    astNodes = getAstNodes()
    return (assignInfo, astNodes)

def getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo):
    for funcName in assignInfo:
        for varName in assignInfo[funcName]:
            varInfoObj = assignInfo[funcName][varName]
            if (len(varInfoObj.getHashArgsInAssignNode()) > 0):
                return True

    return False

def getVarTypeFromVarName_EC(varName, funcName):
    if DEBUG : print("getVarTypeFromVarName_EC:  varName and funcName are ", varName, " and ", funcName)

    varType_SDL = getVarTypeFromVarName(varName, funcName, False, False)
    if (varType_SDL == types.NO_TYPE):
        sys.exit("getVarTypeFromVarName_EC in SDLtoECConvert.py:  getVarTypeFromVarName returned types.NO_TYPE for variable name " + str(varName) + " and function name " + str(funcName) + ".")

    varType_EC = convertTypeSDLtoEC(varType_SDL)
    return varType_EC

def writeVarDecls(outputECFile, oldFuncName, assignInfo, listOfVarsToNotInclude):
    if (oldFuncName not in assignInfo):
        sys.exit("writeVarDecls in SDLtoECConvert.py:  oldFuncName not in assignInfo.")

    outputString = ""

    for varName in assignInfo[oldFuncName]:
        if (varName == inputKeyword):
            continue

        if (varName in listOfVarsToNotInclude):
            continue

        #for some reason, SDLParser says variables of type "bool" are actually of type "int".
        #Here's a workaround to fix that
        assignNodeRight = str(assignInfo[oldFuncName][varName].getAssignNode().right)
        if ( (assignNodeRight == trueKeyword_SDL) or (assignNodeRight == falseKeyword_SDL) ):
            outputString += "    " + varKeyword_EC + " " + varName + " : " + booleanType_EC + ";\n"
            continue

        varType_EC = getVarTypeFromVarName_EC(varName, oldFuncName)

        outputString += "    " + varKeyword_EC + " " + varName + " : " + varType_EC + ";\n"

    if (len(outputString) > 0):
        outputECFile.write(outputString)

def writeBodyOfFunc(outputECFile, oldFuncName, astNodes, config, assignStmtsToNotInclude):
    startLineNoOfFunc = getStartLineNoOfFunc(oldFuncName)
    endLineNoOfFunc = getEndLineNoOfFunc(oldFuncName)

    startLineNoOfBody = startLineNoOfFunc + 2
    endLineNoOfBody = endLineNoOfFunc - 1

    writeAstNodesToFile(outputECFile, astNodes, startLineNoOfBody, endLineNoOfBody, config, assignStmtsToNotInclude)

def isAssignStmt(astNode):
    if (astNode.type == ops.EQ):
        return True

    return False

def makeSDLtoECVarNameReplacements(attrAsString, config):
    if (attrAsString == config.messageName_SDL):
        return messageName_EC
    if (attrAsString == config.secretKeyName_SDL):
        return secretKeyName_EC
    return attrAsString

def getAssignStmtAsString(astNode, config):
    if (astNode.type == ops.ATTR):
        attrAsString = str(astNode)
        #attrAsString = makeSDLtoECVarNameReplacements(attrAsString, config)
        return attrAsString
    elif (astNode.type == ops.TYPE):
        groupTypeAsString = str(astNode)
        if (groupTypeAsString not in validGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received node of type ops.TYPE, but it is not a valid type.")
        return groupTypeAsString
    elif (astNode.type == ops.EXP):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        return "(" + leftSide + " " + expOp_EC + " " + rightSide + ")"
    elif (astNode.type == ops.PAIR):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        return "e(" + leftSide + ", " + rightSide + ")"
    elif (astNode.type == ops.EQ):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        return leftSide + " " + assignmentOperator_EC + " " + rightSide
    elif (astNode.type == ops.EQ_TST):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        return "(" + leftSide + " " + eqTstOperator_EC + " " + rightSide + ")"
    elif (astNode.type == ops.HASH):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        if (rightSide not in validHashGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received invalid type for hash call.")
        #return hashFuncName_EC + "(" + leftSide + ", " + rightSide + ")"
        return hashFuncName_EC + "(" + leftSide + ")"
    elif (astNode.type == ops.RANDOM):
        randomGroupType = getAssignStmtAsString(astNode.left, config)
        if (randomGroupType not in validRandomGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received invalid type for random call.")
        if ( (randomGroupType == str(types.G1)) or (randomGroupType == str(types.G2)) ):
            return randomG1GenerationStmt_EC
        elif (randomGroupType == str(types.ZR)):
            return randomZRGenerationStmt_EC
        else:
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  error in system logic for random calls.")
    else:
        sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  could not handle this type (" + str(astNode.type) + ") of node (" + str(astNode) + ").  Need to add more logic to support it.")

def isUnnecessaryNode(astNode):
    if ( (astNode.type == ops.BEGIN) and (astNode.left.attr == IF_BRANCH_HEADER) ):
        return True

    return False

def isIfStmtStart(astNode):
    if (astNode.type == ops.IF):
        return True

    return False

def getIfStmtDecl(astNode, config):
    outputString = ""

    outputString += "if("
    outputString += getAssignStmtAsString(astNode.left, config)
    outputString += ") {"

    return outputString

def getIfStmtEnd(astNode):
    return "}"

def isIfStmtEnd(astNode):
    if ( (astNode.type == ops.END) and (astNode.left.attr == IF_BRANCH_HEADER) ):
        return True

    return False

def isElseStmtStart(astNode):
    if (astNode.type == ops.ELSE):
        return True

    return False

def isNONENode(astNode):
    if (astNode.type == ops.NONE):
        return True

    return False

def getElseStmtStart(astNode, config):
    outputString = ""

    if (astNode.left == None):
        outputString += "else {"
    else:
        outputString += "else if ("
        outputString += getAssignStmtAsString(astNode.left, config)
        outputString += ") {"

    return outputString

def isAssignStmtToNotInclude(astNode, config, assignStmtsToNotInclude):
    if (isAssignStmt(astNode) == False):
        return False

    varNameToBeAssigned = getAssignStmtAsString(astNode.left, config)

    if (varNameToBeAssigned in assignStmtsToNotInclude):
        return True

    return False

def writeAstNodesToFile(outputECFile, astNodes, startLineNo, endLineNo, config, assignStmtsToNotInclude):
    outputString = ""
    currentNumSpaces = (numSpacesForIndent * 2)

    for lineNo in range(startLineNo, (endLineNo + 1)):
        currentAstNode = astNodes[(lineNo - 1)]
        if (isAssignStmtToNotInclude(currentAstNode, config, assignStmtsToNotInclude) == True):
            continue
        elif (isAssignStmt(currentAstNode) == True):
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getAssignStmtAsString(currentAstNode, config)
            outputString += endOfLineOperator_EC
        elif (isIfStmtStart(currentAstNode) == True):
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getIfStmtDecl(currentAstNode, config)
            currentNumSpaces += numSpacesForIndent
        elif (isIfStmtEnd(currentAstNode) == True):
            currentNumSpaces -= numSpacesForIndent
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getIfStmtEnd(currentAstNode)
        elif (isElseStmtStart(currentAstNode) == True):
            currentNumSpaces -= numSpacesForIndent
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += "}\n"
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getElseStmtStart(currentAstNode, config)
            currentNumSpaces += numSpacesForIndent
        elif (isUnnecessaryNode(currentAstNode) == True):
            continue
        elif (isNONENode(currentAstNode) == True):
            continue
        else:
            sys.exit("writeAstNodesToFile in SDLtoECConvert.py:  cannot handle this type of AST node (" + str(currentAstNode) + ").  Need to add logic to support it.")
        outputString += "\n"

    outputECFile.write(outputString)

def writeMessageAdditionToQueriedList(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += queriedName_EC + " " + assignmentOperator_EC + " "
    outputString += messageName_EC + " " + appendOperator_EC + " "
    outputString += queriedName_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeReturnValue(outputECFile, funcName, assignInfo):
    if (funcName not in assignInfo):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  funcName parameter passed in is not in assignInfo parameter passed in.")

    if (outputKeyword not in assignInfo[funcName]):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  outputKeyword not in assignInfo[funcName].")

    '''
    outputVarInfoObj = assignInfo[funcName][outputKeyword]

    outputVarDeps = outputVarInfoObj.getVarDeps()

    if ( (len(outputVarDeps) != 1) and (outputVarDeps != [trueKeyword_SDL, falseKeyword_SDL]) ):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  variable dependencies of output keyword does not consist of a list of one element OR a list of [\"True\", \"False\"], which is what is expected.")
    '''

    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += returnKeyword_EC + " "

    '''
    if (len(outputVarDeps) == 1):
        outputString += str(outputVarDeps[0]) + endOfLineOperator_EC + "\n"
    else:
        outputString += outputKeyword + endOfLineOperator_EC + "\n"
    '''

    outputString += outputKeyword + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeFuncEnd(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcEndChar_EC + "\n\n"

    outputECFile.write(outputString)

def addBoolRetVarForVerifyFunc(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + varNameForVerifyBoolRetVal_EC + " : "
    outputString += booleanType_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def convertSignFunc(outputECFile, config, assignInfo, astNodes):
    writeFuncDecl(outputECFile, config.signFuncName_SDL, signFuncName_EC, config, assignInfo)
    writeVarDecls(outputECFile, config.signFuncName_SDL, assignInfo, [])
    writeCountVarIncrement(outputECFile, signFuncName_EC)
    writeBodyOfFunc(outputECFile, config.signFuncName_SDL, astNodes, config, [])
    writeMessageAdditionToQueriedList(outputECFile)
    writeReturnValue(outputECFile, config.signFuncName_SDL, assignInfo)
    writeFuncEnd(outputECFile)

def convertVerifyFunc(outputECFile, config, assignInfo, astNodes):
    writeFuncDecl(outputECFile, config.verifyFuncName_SDL, verifyFuncName_EC, config, assignInfo)
    writeVarDecls(outputECFile, config.verifyFuncName_SDL, assignInfo, [])
    #addBoolRetVarForVerifyFunc(outputECFile)
    writeCountVarIncrement(outputECFile, verifyFuncName_EC)
    writeBodyOfFunc(outputECFile, config.verifyFuncName_SDL, astNodes, config, [])
    writeReturnValue(outputECFile, config.verifyFuncName_SDL, assignInfo)
    writeFuncEnd(outputECFile)

def getTypeOfOutputVar(funcName, assignInfo):
    '''
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    outputVars = inputOutputVarsDict[outputKeyword]
    if (len(outputVars) != 1):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  number of output variables of function is unequal to one; not supported.")

    if (outputVars[0] == "False"):
        return booleanType_EC

    outputType_EC = getVarTypeFromVarName_EC(outputVars[0], funcName)
    return outputType_EC
    '''
    if (funcName not in assignInfo):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  function name parameter passed in is not in assignInfo parameter passed in.")

    if (outputKeyword not in assignInfo[funcName]):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  output keyword is not in assignInfo[funcName] parameters passed in.")
 
    return getVarTypeFromVarName_EC(outputKeyword, funcName)

def convertTypeSDLtoEC_Strings(outputType_SDL):
    if (outputType_SDL == "G1"):
        return "G_1"
    if (outputType_SDL == "G2"):
        return "G_1"
    if (outputType_SDL == "GT"):
        return "G_T"
    if (outputType_SDL == "ZR"):
        return "Z_R"
    if (outputType_SDL == "int"):
        return "int"
    if (outputType_SDL == "bool"):
        return booleanType_EC

    sys.exit("convertTypeSDLtoEC_Strings in SDLtoECConvert.py:  outputType_SDL " + str(outputType_SDL) + " is not of a type we support; need to add more logic to support it.")

def convertTypeSDLtoEC(outputType_SDL):
    if (outputType_SDL == types.G1):
        return "G_1"
    if (outputType_SDL == types.G2):
        return "G_1"
    if (outputType_SDL == types.GT):
        return "G_T"
    if (outputType_SDL == types.ZR):
        return "Z_R"
    if (outputType_SDL == types.int):
        return "int"
    if (outputType_SDL == types.bool):
        return booleanType_EC

    sys.exit("convertTypeSDLtoEC in SDLtoECConvert.py:  outputType_SDL " + str(outputType_SDL) + " is not of a type we support; need to add more logic to support it.")

def writeFuncDecl(outputECFile, oldFuncName, newFuncName, config, assignInfo):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " " + newFuncName + "("
    outputString += getLineOfInputParams(oldFuncName, config, assignInfo)
    outputString += ") : "
    outputString += getTypeOfOutputVar(oldFuncName, assignInfo)
    outputString += " " + assignmentOperator_EC + " " + funcStartChar_EC + "\n"

    outputECFile.write(outputString)

def getLineOfInputParams(funcName, config, assignInfo):
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    
    outputString = ""

    for varName in inputOutputVarsDict[inputKeyword]:
        if DEBUG : print("getLineOfInputParams:  variable name is ", str(varName))

        outputString += getECVarNameAndTypeFromSDLName(varName, config, assignInfo, funcName)
        if (len(outputString) > 0):
            outputString += ", "

    lenOutputString = len(outputString)

    if (outputString[(lenOutputString - 2):lenOutputString] == ", "):
        outputString = outputString[0:(lenOutputString - len(", "))]

    return outputString

def getECVarNameAndTypeFromSDLName(varName, config, assignInfo, funcName):

    if (funcName not in assignInfo):
        sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  funcName not in assignInfo.")

    #if (varName not in assignInfo[funcName][varName]):
        #sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  varName not in assignInfo[funcName].")

    #in EC, secret key is global, so no need to declare it here
    if (varName == config.secretKeyName_SDL):
        return ""

    if (varName == config.messageName_SDL):
        return messageName_EC + " : " + messageType_EC

    if DEBUG : print("getECVarNameAndTypeFromSDLName:  varName and funcName are ", varName, " and ", funcName)

    varType_EC = getVarTypeFromVarName_EC(varName, funcName)

    return varName + " : " + varType_EC

    sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  could not handle case of varName (" + str(varName) + ") passed in.  Need to add more logic for it.")

def addAdvAbstractDef(outputECFile, atLeastOneHashCall, assignInfo, config):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += abstractKeyword_EC + " " + adversaryIdentifier_EC + " "
    outputString += assignmentOperator_EC + " " + adversarySignatureIdentifier_EC + funcStartChar_EC

    if (atLeastOneHashCall == True):
        outputString += hashFuncName_EC + ", "

    outputString += signFuncName_EC 

    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    if (len(extraFuncsForAdversary) == 0):
        outputString += funcEndChar_EC + "\n\n"
        outputECFile.write(outputString)
        return

    for extraFunc in extraFuncsForAdversary:
        outputString += ", "
        outputString += extraFunc

    outputString += funcEndChar_EC + "\n\n"
    outputECFile.write(outputString)

def writeVerifyArgsDeclForMain(outputECFile, config, assignInfo):
    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    listOfVarsToNotDeclare = []

    for publicKeyVar in publicKeyVars:
        if (publicKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(publicKeyVar)

    for secretKeyVar in secretKeyVars:
        if (secretKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(secretKeyVar)

    if (outputKeyword not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(outputKeyword)

    if (config.verifyFuncName_SDL not in assignInfo):
        sys.exit("writeVerifyArgsDeclForMain in SDLtoECConvert.py:  verify function name from SDL is not in assignInfo.")

    if (inputKeyword not in assignInfo[config.verifyFuncName_SDL]):
        sys.exit("writeVerifyArgsDeclForMain in SDLtoECConvert.py:  input keyword is not in assignInfo[verify func name from SDL].")

    inputVarInfoObj = assignInfo[config.verifyFuncName_SDL][inputKeyword]
    
    if (inputVarInfoObj == None):
        sys.exit("writeVerifyArgsDeclForMain in SDLtoECConvert.py:  input variable information object extracted from assignInfo[verify function name from SDL] is None.")

    inputVarNamesList = []

    if ( (inputVarInfoObj.getIsList() == True) and (len(inputVarInfoObj.getListNodesList()) > 0) ):
        for inputVarName in inputVarInfoObj.getListNodesList():
            if (inputVarName in inputVarNamesList):
                sys.exit("writeVerifyArgsDeclForMain in SDLtoECConvert.py:  duplicate variable names found in input variable names.")

            inputVarNamesList.append(inputVarName)

    outputString = ""

    for inputVarName in inputVarNamesList:
        if (inputVarName in listOfVarsToNotDeclare):
            continue

        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += varKeyword_EC + " "
        outputString += getECVarNameAndTypeFromSDLName(inputVarName, config, assignInfo, config.verifyFuncName_SDL)
        outputString += endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeMainFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " Main() : " + booleanType_EC + " " + assignmentOperator_EC + " "
    outputString += funcStartChar_EC + "\n"

    outputECFile.write(outputString)

    '''
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + messageVarNameInMain_EC + " : " + messageType_EC
    outputString += endOfLineOperator_EC + "\n"
    '''

    writeVerifyArgsDeclForMain(outputECFile, config, assignInfo)

    '''
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + sVarInMain_EC + " : G_1" + endOfLineOperator_EC + "\n"
    '''

    #outputECFile.write(outputString)

    writeExtraVarsNeededForMain(outputECFile, config, assignInfo)
    writeCallToInit(outputECFile)
    writeCallToAbstractAdversaryFunction(outputECFile)

def writeCallToAbstractAdversaryFunction(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += "("

    #(m, s) = A(pk);

    outputECFile.write(outputString)

def writeCallToInit(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += dummyVarInMain_EC + " " + assignmentOperator_EC + " " + initFuncName_EC 
    outputString += "();\n"

    outputECFile.write(outputString)

def writeExtraVarsNeededForMain(outputECFile, config, assignInfo):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + sVarInMain_EC + " : "
    groupTypeOfSignatureVariable = getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config)
    outputString += groupTypeOfSignatureVariable + ";\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + vVarInMain_EC + " : " + booleanType_EC + ";\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + dummyVarInMain_EC + " : " + booleanType_EC + ";\n\n"

    outputECFile.write(outputString)

def initializeCountVars(outputECFile, config, assignInfo):
    allFuncsWithCountVars = getExtraFuncsForAdversary(assignInfo, config)
    allFuncsWithCountVars.append(hashFuncName_EC)
    allFuncsWithCountVars.append(signFuncName_EC)
    allFuncsWithCountVars.append(verifyFuncName_EC)

    outputString = ""

    for funcName in allFuncsWithCountVars:
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += countVarPrefix + funcName + " = 0;\n"

    outputECFile.write(outputString)

def writeInitFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " Init() : " + booleanType_EC + " = {\n"

    outputECFile.write(outputString)

    initializeCountVars(outputECFile, config, assignInfo)

    convertKeygenFunc(outputECFile, config, assignInfo, astNodes)

    outputString = ""

    if (atLeastOneHashCall == True):
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += randomOracleVarName_EC + " " + assignmentOperator_EC + " " + emptyMapName_EC
        outputString += endOfLineOperator_EC + "\n"
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += queriedName_EC + " " + assignmentOperator_EC + " " + emptyMapSymbol_EC
        outputString += endOfLineOperator_EC + "\n"
        outputECFile.write(outputString)

    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += returnKeyword_EC + " " + trueKeyword_EC + endOfLineOperator_EC + "\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcEndChar_EC + "\n\n"
    outputECFile.write(outputString)

def convertKeygenFunc(outputECFile, config, assignInfo, astNodes):
    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    listOfVarsToNotDeclare = []

    for publicKeyVar in publicKeyVars:
        if (publicKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(publicKeyVar)

    for secretKeyVar in secretKeyVars:
        if (secretKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(secretKeyVar)

    if (outputKeyword not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(outputKeyword)

    writeVarDecls(outputECFile, config.keygenFuncName_SDL, assignInfo, listOfVarsToNotDeclare)
    writeBodyOfFunc(outputECFile, config.keygenFuncName_SDL, astNodes, config, [outputKeyword])

def getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config):
    if (config.signFuncName_SDL not in assignInfo):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  the function name of the sign function from the config file is not in assignInfo.")

    if (outputKeyword not in assignInfo[config.signFuncName_SDL]):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  output keyword is not in assignInfo[config.signFuncName_SDL].")

    varDepsOfOutputKeyword = assignInfo[config.signFuncName_SDL][outputKeyword].getVarDeps()
    if (len(varDepsOfOutputKeyword) != 1):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  length of variable dependencies list of output variable is unequal to 1 (currently unsupported).")

    outputVariable = varDepsOfOutputKeyword[0]
    if (outputVariable not in assignInfo[config.signFuncName_SDL]):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  output variable found is not assigned anywhere in the sign function.")

    return getVarTypeFromVarName_EC(outputVariable, config.signFuncName_SDL)

def getExtraFuncsForAdversary(assignInfo, config):
    retList = []

    for keyName in assignInfo:
        if ( (keyName not in funcNamesAdvDoesntNeed) and (keyName != config.keygenFuncName_SDL) and (keyName != config.signFuncName_SDL) and (keyName != config.verifyFuncName_SDL) ):
            if (keyName not in retList):
                retList.append(keyName)

    return retList

def getHashGroupTypeOfNodeRecursive(inputNode, hashesGroupTypesInFunc):
    if (inputNode.type == ops.HASH):
        groupTypeToAdd = str(inputNode.right)
        if (len(hashesGroupTypesInFunc) == 0):
            hashesGroupTypesInFunc.append(groupTypeToAdd)
        else:
            if (groupTypeToAdd not in hashesGroupTypesInFunc):
                sys.exit("getHashGroupTypeOfNodeRecursive in SDLtoECConvert.py:  found mismatching hash types in same function.")

    if (inputNode.left != None):
        getHashGroupTypeOfNodeRecursive(inputNode.left, hashesGroupTypesInFunc)

    if (inputNode.right != None):
        getHashGroupTypeOfNodeRecursive(inputNode.right, hashesGroupTypesInFunc)

def getHashGroupTypeOfNode(inputNode, hashesGroupTypesInFunc):
    getHashGroupTypeOfNodeRecursive(inputNode, hashesGroupTypesInFunc)

def getHashGroupTypeOfFunc(funcName, assignInfo, config):
    if (funcName not in assignInfo):
        sys.exit("getHashGroupTypeOfFunc in SDLtoECConvert.py:  function name parameter passed in isn't in assignInfo parameter passed in.")

    hashesGroupTypesInFunc = []

    for varName in assignInfo[funcName]:
        varInfoObj = assignInfo[funcName][varName]
        assignNodeRight = varInfoObj.getAssignNode().right
        hashGroupTypeOfNode = getHashGroupTypeOfNode(assignNodeRight, hashesGroupTypesInFunc)

    if (len(hashesGroupTypesInFunc) > 1):
        sys.exit("getHashGroupTypeOfFunc in SDLtoECConvert.py:  length of hashesGroupTypesInFunc data structure returned is greater than one.")

    if (len(hashesGroupTypesInFunc) == 0):
        return None

    return hashesGroupTypesInFunc[0]

def getInputVarsForFunc(outputECFile, assignInfo, config, funcName):
    if (funcName not in assignInfo):
        sys.exit("getInputVarsForFunc in SDLtoECConvert.py:  function name passed in is not in assignInfo parameter passed in.")

    outputString = ""

    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)

    for varName in inputOutputVarsDict[inputKeyword]:
        #in EC, secret key is global, so no need to declare it here
        if (varName == config.secretKeyName_SDL):
            continue

        if (varName == config.messageName_SDL):
            outputString += messageType_EC + ", "
            continue

        varType_EC = getVarTypeFromVarName_EC(varName, funcName)
        outputString += varType_EC + ", "

    lenOutputString = len(outputString)
    outputString = outputString[0:(lenOutputString - len(", "))]

    return outputString

def addAdversaryDeclLineToOutputECFile(outputECFile, assignInfo, config):
    groupTypeOfSignatureVariable = getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config)

    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    outputString = ""
    outputString += adversaryKeyword_EC + " " + adversaryVarName_EC + " (" + advPubKeyVarName_EC + " : "

    pubKeyType = getVarTypeFromVarName_EC(config.publicKeyName_SDL, config.keygenFuncName_SDL)

    outputString += pubKeyType + ") : (" + messageType_EC + " * " + groupTypeOfSignatureVariable + ") {"
    outputString += messageType_EC + " -> "

    hashGroupTypeOfSigFunc_SDL = getHashGroupTypeOfFunc(config.signFuncName_SDL, assignInfo, config)
    hashGroupTypeOfSigFunc_EC = convertTypeSDLtoEC_Strings(hashGroupTypeOfSigFunc_SDL)

    outputString += hashGroupTypeOfSigFunc_EC + "; ("

    outputECFile.write(outputString)
    outputString = ""

    # write input vars for sign function
    outputString += getInputVarsForFunc(outputECFile, assignInfo, config, config.signFuncName_SDL)

    outputString += ") -> "

    outputTypeOfSignFunc = getTypeOfOutputVar(config.signFuncName_SDL, assignInfo)
    outputString += outputTypeOfSignFunc

    outputECFile.write(outputString)
    outputString = ""

    if (len(extraFuncsForAdversary) == 0):
        outputString += "}."
        outputString += "\n\n"
        outputECFile.write(outputString)
        return

    for extraFunc in extraFuncsForAdversary:
        outputString += "; ("
        outputString += getInputVarsForFunc(outputECFile, assignInfo, config, extraFunc)
        outputString += ") -> "
        outputTypeOfFunc = getTypeOfOutputVar(extraFunc, assignInfo)
        outputString += outputTypeOfFunc

    outputString += "}.\n\n"

    outputECFile.write(outputString)

def writeExtraFuncsForAdversary(outputECFile, assignInfo, config, astNodes):
    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    if (len(extraFuncsForAdversary) == 0):
        return

    for extraFunc in extraFuncsForAdversary:
        writeFuncDecl(outputECFile, extraFunc, extraFunc, config, assignInfo)
        writeVarDecls(outputECFile, extraFunc, assignInfo, [])
        writeCountVarIncrement(outputECFile, extraFunc)
        writeBodyOfFunc(outputECFile, extraFunc, astNodes, config, [])
        writeReturnValue(outputECFile, extraFunc, assignInfo)
        writeFuncEnd(outputECFile)

def addCountVars(outputECFile, assignInfo, config, atLeastOneHashCall):
    outputString = ""

    allFuncsWithCountVars = getExtraFuncsForAdversary(assignInfo, config)

    currentNumSpacesToUse = numSpacesForIndent

    if (atLeastOneHashCall == True):
        outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
        outputString += varKeyword_EC + " " + countVarPrefix + hashFuncName_EC + " : " + intType_EC + "\n"

    allFuncsWithCountVars.append(signFuncName_EC)
    allFuncsWithCountVars.append(verifyFuncName_EC)

    for countVarFuncName in allFuncsWithCountVars:
        outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
        outputString += varKeyword_EC + " " + countVarPrefix + countVarFuncName + " : " + intType_EC + "\n"

    outputECFile.write(outputString)

def writeCountVarIncrement(outputECFile, funcName):
    outputString = ""
    currentNumSpacesToUse = 4
    outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
    outputString += countVarPrefix + funcName + " " + assignmentOperator_EC + " "
    outputString += countVarPrefix + funcName + " " + additionOperator_EC + " 1\n"
    outputECFile.write(outputString)

def main(inputSDLFileName, configName, outputECFileName, debugOrNot):
    global DEBUG

    if (debugOrNot == "True"):
        DEBUG = True
    elif (debugOrNot == "False"):
        DEBUG = False
    else:
        sys.exit("main in SDLtoECConvert.py:  DEBUG parameter from command line was specified incorrectly (two options are True and False).")


    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    config = importlib.import_module(configName)

    atLeastOneHashCall = False

    (assignInfo, astNodes) = getInputSDLFileMetadata(inputSDLFileName)

    addTemplateLinesToOutputECFile(outputECFile)

    addAdversaryDeclLineToOutputECFile(outputECFile, assignInfo, config)

    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile, assignInfo, config)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo)

    addCountVars(outputECFile, assignInfo, config, atLeastOneHashCall)

    if (atLeastOneHashCall == True):
        addStatementsForPresenceOfHashes(outputECFile, assignInfo, config)

    convertSignFunc(outputECFile, config, assignInfo, astNodes)

    writeExtraFuncsForAdversary(outputECFile, assignInfo, config, astNodes)

    addAdvAbstractDef(outputECFile, atLeastOneHashCall, assignInfo, config)

    convertVerifyFunc(outputECFile, config, assignInfo, astNodes)

    writeInitFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall)

    writeMainFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall)

    #convertKeygenFunc(outputECFile, config, assignInfo, astNodes)

    inputSDLFile.close()
    outputECFile.close()

def printErrorMessageAndExit():
    sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [SCHEMENAME.config] [name of output EasyCrypt file] [Print DEBUG info (True or False)]]")

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 5) or (lenSysArgv > 5) ):
        printErrorMessageAndExit()

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        printErrorMessageAndExit()

    main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
