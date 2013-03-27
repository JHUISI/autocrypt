import sdlpath
from sdlparser.SDLParser import *
import re

templateFileName = "/home/easycrypt/Desktop/autocrypt/ECTemplate.txt"

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
    outputString += "_EF = {\n"

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
    outputString = "  var secret_key : int\n"
    outputString += "  var queried : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  var rand_oracle : (message, G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile):
    outputString = "\n  fun Hash(m : message) : G_1 = {\n"
    outputString += "    if(!in_dom(m, rand_oracle)) {\n"
    outputString += "      rand_oracle[m] = Rand_G_1();\n"
    outputString += "    }\n"
    outputString += "    return rand_oracle[m];\n"
    outputString += "  }\n"

    outputECFile.write(outputString)

def addStatementsForPresenceOfHashes(outputECFile):
    addGlobalVarsForHashes(outputECFile)
    addHashFuncDef(outputECFile)

def main(inputSDLFileName, outputECFileName):
    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    atLeastOneHashCall = False

    addTemplateLinesToOutputECFile(outputECFile)
    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot(inputSDLFile)
    if (atLeastOneHashCall == True):
        addStatementsForPresenceOfHashes(outputECFile)

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 3) or (lenSysArgv > 3) ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    main(sys.argv[1], sys.argv[2])
