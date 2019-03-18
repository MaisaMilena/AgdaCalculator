# Calculator in Agda compiled to JS

A calculator created in Agda and compiled to JS.
- use [JavaScript Backend](https://agda.readthedocs.io/en/v2.5.4.2/tools/compilers.html): translates Agda code to JavaScript code.

### Requirements
- must disable the agda-stdlib by editing ```~/.agda/defaults```
- have node.js installed


```
# JavaScript backend is used to translate Agda code to JavaScript code
agda --js --compile-dir=node_modules src/Calculator.agda
# Use node to execute the program   
node node_modules/jAgda.Calculator.js
```
