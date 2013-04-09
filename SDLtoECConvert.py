import sdlpath
from sdlparser.SDLParser import *
import re, importlib

templateFileName = "ECTemplate.txt"
configFileName = "SDLtoECConfig"
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
validGroupTypes = ["G1", "G2", "GT", "ZR"]
validHashGroupTypes = ["G1", "G2", "ZR"]

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

def addGlobalVars(outputECFile):
    outputString = "  var " + secretKeyName_EC + " : int\n"
    outputString += "  var " + queriedName_EC + " : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  var rand_oracle : (message, G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile):
    outputString = "\n  fun "+ hashFuncName_EC + "(m : message) : G_1 = {\n"
    outputString += "    if(!in_dom(m, rand_oracle)) {\n"
    outputString += "      rand_oracle[m] = Rand_G_1();\n"
    outputString += "    }\n"
    outputString += "    return rand_oracle[m];\n"
    outputString += "  }\n\n"

    outputECFile.write(outputString)

def addStatementsForPresenceOfHashes(outputECFile):
    addGlobalVarsForHashes(outputECFile)
    addHashFuncDef(outputECFile)

def getInputSDLFileMetadata(inputSDLFileName):
    parseFile2(inputSDLFileName, False, True)
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

    varType_EC = convertGroupTypeSDLtoEC(varType_SDL)
    return varType_EC

def writeVarDecls(outputECFile, oldFuncName, assignInfo):
    if (oldFuncName not in assignInfo):
        sys.exit("writeVarDecls in SDLtoECConvert.py:  oldFuncName not in assignInfo.")

    outputString = ""

    for varName in assignInfo[oldFuncName]:
        if ( (varName == inputKeyword) or (varName == outputKeyword) ):
            continue

        varType_EC = getVarTypeFromVarName_EC(varName, oldFuncName)

        outputString += "    " + varKeyword_EC + " " + varName + " : " + varType_EC + ";\n"

    if (len(outputString) > 0):
        outputECFile.write(outputString)

def writeBodyOfFunc(outputECFile, oldFuncName, astNodes, config):
    startLineNoOfFunc = getStartLineNoOfFunc(oldFuncName)
    endLineNoOfFunc = getEndLineNoOfFunc(oldFuncName)

    startLineNoOfBody = startLineNoOfFunc + 2
    endLineNoOfBody = endLineNoOfFunc - 2

    writeAstNodesToFile(outputECFile, astNodes, startLineNoOfBody, endLineNoOfBody, config)

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
        attrAsString = makeSDLtoECVarNameReplacements(attrAsString, config)
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
    elif (astNode.type == ops.EQ):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        return leftSide + " " + assignmentOperator_EC + " " + rightSide
    elif (astNode.type == ops.HASH):
        leftSide = getAssignStmtAsString(astNode.left, config)
        rightSide = getAssignStmtAsString(astNode.right, config)
        if (rightSide not in validHashGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received invalid type for hash call.")
        #return hashFuncName_EC + "(" + leftSide + ", " + rightSide + ")"
        return "(" + hashFuncName_EC + "(" + leftSide + "))"
    else:
        sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  could not handle this type (" + str(astNode.type) + ") of node (" + str(astNode) + ").  Need to add more logic to support it.")

def writeAstNodesToFile(outputECFile, astNodes, startLineNo, endLineNo, config):
    outputString = ""
    currentNumSpaces = 4

    for lineNo in range(startLineNo, (endLineNo + 1)):
        currentAstNode = astNodes[(lineNo - 1)]
        outputString += writeNumOfSpacesToString(currentNumSpaces)
        if (isAssignStmt(currentAstNode) == True):
            outputString += getAssignStmtAsString(currentAstNode, config)
            outputString += endOfLineOperator_EC
        else:
            sys.exit("writeAstNodesToFile in SDLtoECConvert.py:  cannot handle this type of AST node (" + str(currentAstNode) + ").  Need to add logic to support it.")
        outputString += "\n"

    outputECFile.write(outputString)

def writeMessageAdditionToQueriedList(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(4)
    outputString += queriedName_EC + " " + assignmentOperator_EC + " "
    outputString += messageName_EC + " " + appendOperator_EC + " "
    outputString += queriedName_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeReturnValue(outputECFile, funcName, assignInfo):
    if (funcName not in assignInfo):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  funcName parameter passed in is not in assignInfo parameter passed in.")

    if (outputKeyword not in assignInfo[funcName]):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  outputKeyword not in assignInfo[funcName].")

    outputVarInfoObj = assignInfo[funcName][outputKeyword]

    outputVarDeps = outputVarInfoObj.getVarDeps()
    if (len(outputVarDeps) != 1):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  variable dependencies of output keyword does not consist of a list of one element, which is what is expected.")

    outputString = ""
    outputString += writeNumOfSpacesToString(4)
    outputString += returnKeyword_EC + " "
    outputString += str(outputVarDeps[0]) + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeFuncEnd(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(2)
    outputString += funcEndChar_EC + "\n\n"

    outputECFile.write(outputString)

def addBoolRetVarForVerifyFunc(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(4)
    outputString += varKeyword_EC + " " + varNameForVerifyBoolRetVal_EC + " : "
    outputString += booleanType_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def convertSignFunc(outputECFile, config, assignInfo, astNodes):
    writeFuncDecl(outputECFile, config.signFuncName_SDL, signFuncName_EC, config, assignInfo)
    writeVarDecls(outputECFile, config.signFuncName_SDL, assignInfo)
    writeBodyOfFunc(outputECFile, config.signFuncName_SDL, astNodes, config)
    writeMessageAdditionToQueriedList(outputECFile)
    writeReturnValue(outputECFile, config.signFuncName_SDL, assignInfo)
    writeFuncEnd(outputECFile)

def convertVerifyFunc(outputECFile, config, assignInfo, astNodes):
    writeFuncDecl(outputECFile, config.verifyFuncName_SDL, verifyFuncName_EC, config, assignInfo)
    writeVarDecls(outputECFile, config.verifyFuncName_SDL, assignInfo)
    addBoolRetVarForVerifyFunc(outputECFile)
    writeBodyOfFunc(outputECFile, config.verifyFuncName_SDL, astNodes, config)

def getTypeOfOutputVar(funcName):
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    outputVars = inputOutputVarsDict[outputKeyword]
    if (len(outputVars) != 1):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  number of output variables of function is unequal to one; not supported.")

    if (outputVars[0] == "False"):
        return booleanType_EC

    outputType_EC = getVarTypeFromVarName_EC(outputVars[0], funcName)
    return outputType_EC

def convertGroupTypeSDLtoEC(outputType_SDL):
    if (outputType_SDL == types.G1):
        return "G_1"
    if (outputType_SDL == types.G2):
        return "G_1"
    if (outputType_SDL == types.GT):
        return "G_T"

    sys.exit("convertGroupTypeSDLtoEC in SDLtoECConvert.py:  outputType_SDL " + str(outputType_SDL) + " is not of a type we support; need to add more logic to support it.")

def writeFuncDecl(outputECFile, oldFuncName, newFuncName, config, assignInfo):
    outputString = ""
    outputString += "  fun " + newFuncName + "("
    outputString += getLineOfInputParams(oldFuncName, config, assignInfo)
    outputString += ") : "
    outputString += getTypeOfOutputVar(oldFuncName)
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

def addAdvAbstractDef(outputECFile, atLeastOneHashCall):
    outputString = ""
    outputString += writeNumOfSpacesToString(2)
    outputString += abstractKeyword_EC + " " + adversaryIdentifier_EC + " "
    outputString += assignmentOperator_EC + " " + adversarySignatureIdentifier_EC + funcStartChar_EC

    if (atLeastOneHashCall == True):
        outputString += hashFuncName_EC + ", "

    outputString += signFuncName_EC + funcEndChar_EC + "\n\n"

    outputECFile.write(outputString)

def main(inputSDLFileName, outputECFileName, debugOrNot):
    global DEBUG

    if (debugOrNot == "True"):
        DEBUG = True
    elif (debugOrNot == "False"):
        DEBUG = False
    else:
        sys.exit("main in SDLtoECConvert.py:  DEBUG parameter from command line was specified incorrectly (two options are True and False).")


    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    config = importlib.import_module(configFileName)

    atLeastOneHashCall = False

    (assignInfo, astNodes) = getInputSDLFileMetadata(inputSDLFileName)

    addTemplateLinesToOutputECFile(outputECFile)
    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo)
    if (atLeastOneHashCall == True):
        addStatementsForPresenceOfHashes(outputECFile)

    convertSignFunc(outputECFile, config, assignInfo, astNodes)

    addAdvAbstractDef(outputECFile, atLeastOneHashCall)

    convertVerifyFunc(outputECFile, config, assignInfo, astNodes)

    inputSDLFile.close()
    outputECFile.close()

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 4) or (lenSysArgv > 4) ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file] [Print DEBUG info (True or False)]]")

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file] [Print DEBUG info (True or False)]")

    main(sys.argv[1], sys.argv[2], sys.argv[3])
