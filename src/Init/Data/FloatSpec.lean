-- Project linters (prefer grind over omega, etc.)
import FloatSpec.Linter.OmegaLinter

-- Core floating-point functionality
import FloatSpec.Core

-- Calculation modules  
import FloatSpec.Calc

-- Property analysis and error bounds
import FloatSpec.Prop
-- VCFloat-style error bound scaffolding
import FloatSpec.ErrorBound

-- IEEE 754 standard implementation
import FloatSpec.IEEE754

-- Simproc helpers for Id/wp Hoare triples
import FloatSpec.SimprocWP

-- Legacy Pff compatibility
import FloatSpec.Pff

/-!
# FloatSpec

Complete IEEE 754 floating-point formalization in Lean 4
Transformed from the Flocq floating-point library

This library provides:
- Core floating-point functionality and generic formats
- Calculation operations (addition, multiplication, division, square root)
- Property analysis and error bounds 
- Full IEEE 754 standard implementation
- Legacy Pff compatibility layer
-/

/-- Version string for the FloatSpec library -/
def FloatSpec.version : String := "0.7.0"
