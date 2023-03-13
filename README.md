# LLVM-Pass
LLVM is a powerful infrastructure for implementing compilers, and one of its key features is the ability to write custom optimization passes. 
These passes can be used to analyze and transform LLVM IR code in various ways, such as identifying and eliminating dead code, optimizing loops, or performing register allocation.

Observations I made:

1. Pass order matters: LLVM applies passes in a specific order, and the order can affect the effectiveness of each pass. As a result, it's important to carefully consider the order in which passes are applied to get the best results.

2. IR code can be difficult to read: LLVM IR code can be difficult to read and understand, especially for beginners. However, once you become familiar with the syntax and structure of IR code, it becomes easier to write and debug custom passes.

3. Testing is crucial: It's important to thoroughly test custom passes to ensure that they work correctly and do not introduce bugs or unexpected behavior. This can involve creating test cases and using LLVM's testing infrastructure to automate the testing process.
