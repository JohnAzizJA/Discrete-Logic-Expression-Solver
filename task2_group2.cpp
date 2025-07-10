// Original: ((!(A&B) | !C) & (C&A&B)) | (A&C)
// Simplified: A&C

#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cmath>
#include <stdexcept>
using namespace std;

// Function to evaluate expressions without parentheses using the input combination of values
bool evalSubExpression(const string& exp, const unordered_map<char, bool>& inputs){
    int result = -1;
    char op;
    bool inNot = false;

    // Loop through each character in the expression (evaluate from left to right)
    for (char c : exp) {
        if (c == '1' || c == '0') {
            bool value = (c == '1'); // Assign true or false to value according to the value of the character

            // Invert value if it is after a not operator '!'
            if (inNot){
                value = !value;
                inNot = false;
            }

            // Evaluate expression according to the operator
            if (result == -1){
                result = value; // First value is set as the result
            } 
            else{
                if (op == '&'){
                    result = result && value;
                }
                else if (op == '|'){
                    result = result || value;
                }
            }
        } 
        else if (c == '&' || c == '|'){
            op = c; // Set operator
        } 
        else if (c == '!'){
            inNot = true; // Set invert flag if '!' is found
        }
    }

    return result == 1; // Return true if the result is 1, else false
}

// Function to evaluate the complete expressions with or without parentheses
bool evalExpression(const string& exp, const unordered_map<char, bool>& inputs){
    string modifiedExp = exp;
    
    // Replace eachvariable with its corresponding boolean value
    for (char& c: modifiedExp){
        if (isalpha(c)){
            c = inputs.at(c) ? '1' : '0';
        }
    }

    // Evaluate subexpressions in parentheses
    while (modifiedExp.find('(') != string::npos) {
        size_t closePos = modifiedExp.find(')'); // Find index of closing parenthesis
        size_t openPos = modifiedExp.rfind('(', closePos); // Find index of opening parenthesis

        string subExp = modifiedExp.substr(openPos + 1, closePos - openPos - 1); // Extract subexpression

        // Recursively (since there might be another set of parentheses inside a larger expression in parentheses)
        // Evaluate the expression and replace it with result
        bool subResult = evalExpression(subExp, inputs);
        modifiedExp.replace(openPos, closePos - openPos + 1, subResult ? "1" : "0");
    }

    // Evaluate expression after replacing all subexpressions
    return evalSubExpression(modifiedExp, inputs);
}

// Function to extract all variables without duplication
vector<char> getVars(const string& exp){
    vector<char> vars;

    // Loop through each character in the expression
    for (char c: exp){
        if (isalpha(c)){
            c = toupper(c);
            // Check if the variable have already been added to the vector
            bool found = false;
            for (char var: vars){
                if (var == c){
                    found = true;
                    break;
                }
            }
            // Add variable if not found
            if (!found){
                vars.push_back(c);
            }
        }
    }

    // Bubble sort the variables alphabetically
    for (int i = 0; i < vars.size() - 1; i++) {
        for (int j = 0; j < vars.size() - i - 1; j++) {
            if (vars[j] > vars[j + 1]) {
                char temp = vars[j];
                vars[j] = vars[j + 1];
                vars[j + 1] = temp;
            }
        }
    }

    return vars;
}

// Function to record the inputs that make the expression satisfiable (evaluate to true)
void recordSatisfiableInputs(unordered_set<string>& satisfiableInputs, const vector<char> vars, const unordered_map<char, bool>& inputs){
    string inputStr = "";
    // Record the input combination as a string (e.g. -A=1)
    for (char var : vars) {
        inputStr += " -";
        inputStr += var;
        inputStr += "=";
        inputStr += (inputs.at(var) ? '1' : '0');
    }
    satisfiableInputs.insert(inputStr);
}

// Function to handle possible errors
void handleErrors(const string& original, const string& simplified){

    // Ensure the expressions are not empty
    if (original.empty() || simplified.empty()){
        throw invalid_argument("Expressions cannot be empty.");
    }

    // Ensure that no consecutive variables are entered without an operator between them
    for (size_t i = 0; i < original.size() - 1; ++i) {
        if (isalnum(original[i]) && isalnum(original[i + 1])) {
            throw invalid_argument("Original expression has consecutive variables without a gate in between. Please insert a gate (e.g., '&', '|').");
        }
    }
    for (size_t i = 0; i < simplified.size() - 1; ++i) {
        if (isalnum(simplified[i]) && isalnum(simplified[i + 1])) {
            throw invalid_argument("Simplified expression has consecutive variables without a gate in between. Please insert a gate (e.g., '&', '|').");
        }
    }

    // Ensure both expressions have no invalid characters
    for (char c : original) {
        if (!(isalnum(c) || c == '&' || c == '|' || c == '!' || c == '(' || c == ')' || c == ' ')) {
            throw invalid_argument("Original expression contains invalid characters.");
        }
    }
    for (char c : simplified) {
        if (!(isalnum(c) || c == '&' || c == '|' || c == '!' || c == '(' || c == ')' || c == ' ')) {
            throw invalid_argument("Simplified expression contains invalid characters.");
        }
    }

    // Ensure the simplified expression doesn't have more variables than the original
    if (getVars(simplified).size() > getVars(original).size()){
        throw invalid_argument("Simplified expression cannot have more variables than the original expression.");
    }

    // Ensure the simplified expression does not contain variables that are not in the original expression
    for (char var : getVars(simplified)){
        bool found = false;
        for (char oVar: getVars(original)){
            if (oVar == var){
                found = true;
                break;
            }
        }
        if (!found){
            throw invalid_argument("Simplified expression has different variables than the original expression.");
        }
    }
}

// Function to generate the truth table, check equivalence and check satisfiability
void generateTT(const string& original, const string &simplified){
    // Check for errors
    handleErrors(original, simplified);

    cout << "You Entered:-\nOriginal: " << original << "\nSimplified: " << simplified << "\n\n";
    
    // Extract variables
    vector<char> variables = getVars(original);

    int combinations = pow(2, variables.size()); // Calculate the number of possible combinations
    
    // Declare equivalency and satisfiability flags
    bool isEquivalent = true;
    bool isOriginalSatisfiable = false;
    unordered_set<string> originalSatisfiableInputs;
    bool isSimplifiedSatisfiable = false;
    unordered_set<string> simplifiedSatisfiableInputs;

    // Map to store each variable and its corresponding value
    unordered_map<char, bool> inputs;

    // Print header for truth table
    for (char var: variables){
        cout << var << "\t";
    }
    cout << "Original" << "\t" << "Simplified" << "\n";

    // Loop through all possible combinations
    for (int i = 0; i < combinations; i++){
        for (int j = 0; j < variables.size(); j++){
            // Set input values according to the current combination
            inputs[variables[j]] = ((i >> (variables.size() - j - 1)) & 1) == 1;
        }
        
        // Evaluate expressions and store results
        bool resOriginal = evalExpression(original, inputs);
        bool resSimplified = evalExpression(simplified, inputs);

        // Output combination and result in truth table
        for (char var : variables) {
            cout << inputs.at(var) << "\t";
        }
        cout << resOriginal << "\t\t" << resSimplified << "\n";

        // Check equivalence
        if (resOriginal != resSimplified){
            isEquivalent = false;
        }

        // Record satisfiable inputs if the result is true
        if (resOriginal){
            isOriginalSatisfiable = true;
            recordSatisfiableInputs(originalSatisfiableInputs, variables, inputs);
        }
        if (resSimplified){
            isSimplifiedSatisfiable = true;
            recordSatisfiableInputs(simplifiedSatisfiableInputs, variables, inputs);
        }

    }

    // Print satisfiable inputs if the expression is satisfiable
    if (isOriginalSatisfiable) {
        cout << "\nSatisfiable Inputs for Original Expression:\n";
        for (string inputStr : originalSatisfiableInputs) {
            cout << inputStr << endl;
        }
    }
    else {
        cout << "\nOriginal Expression is Unsatisfiable.\n";
    }
    if (isSimplifiedSatisfiable) {
        cout << "\nSatisfiable Inputs for Simplified Expression:\n";
        for (string inputStr : simplifiedSatisfiableInputs) {
            cout << inputStr << endl;
        }
    }
    else {
        cout << "\nSimplified Expression is Unsatisfiable.\n";
    }

    // Print whether the two expressions are equivalent
    if (isEquivalent){
        cout << "\nThe 2 Expressions: '" << original << "' and '" << simplified << "' are Equivalent.\n";
    }
    else{
        cout << "\nThe 2 Expressions: '" << original << "' and '" << simplified << "' are Not Equivalent.\n";
    }
}

int main(){
    try {
        cout << "Please enter the 2 logical expressions in uppercase ('&' for AND - '|' for OR - '!' for NOT):- \n";

        string original, simplified;

        cout << "Enter Original Expression: ";
        getline(cin, original);

        cout << "Enter Simplified Expression: ";
        getline(cin, simplified);

        cout << endl;

        generateTT(original, simplified);
    } 
    catch (const invalid_argument& e) {
        cout << "Error: " << e.what() << endl;
    }
}