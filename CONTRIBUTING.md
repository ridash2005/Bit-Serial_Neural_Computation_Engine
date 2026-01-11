# Contributing to Bit-Serial Neural Computation Engine

Thank you for your interest in contributing to this project! We aim to build a high-performance, resource-efficient neural network accelerator for FPGAs.

## How to Contribute

### 1. Reporting Bugs
*   Check the issue tracker to see if the bug has already been reported.
*   If not, open a new issue with a clear description, steps to reproduce, and expected vs. actual behavior.

### 2. Suggesting Enhancements
*   Open an issue to discuss the enhancement before starting implementation.
*   Clearly explain the use case and the benefit of the proposed change.

### 3. Pull Requests
*   Fork the repository.
*   Create a new branch for your feature or bug fix.
*   Ensure your code follows the coding style guidelines.
*   Submit a pull request with a detailed description of the changes.

## Coding Style Guidelines

### SystemVerilog
*   Use `logic` instead of `reg` or `wire` (where applicable).
*   Avoid `always @(*)`—use `always_comb`, `always_ff`, and `always_latch`.
*   Indent with 4 spaces.
*   Use descriptive names for signals and modules (e.g., `s_axis_tready` instead of `rdy`).
*   Add comments to complex logic or state machines.

### Documentation
*   Keep the architecture and README updated if you modify top-level parameters or interfaces.
