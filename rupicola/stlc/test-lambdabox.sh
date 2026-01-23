#!/usr/bin/env bash
# test-lambdabox.sh - Automated testing script for STLC -> LambdaBox -> Peregrine compilation

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Default values
FSTAR_FILE="LambdaBoxExamples.fst"
EXPRESSION='red_prog nat_program'
OUTPUT_AST="output.ast"
PEREGRINE_TARGET="ocaml"
VERBOSE=false
BYPASS_WF=false

# Usage function
usage() {
    cat <<EOF
Usage: $0 [OPTIONS]

Automated testing script for STLC -> LambdaBox -> Peregrine compilation pipeline.

OPTIONS:
    -f, --file FILE         F* file to evaluate (default: LambdaBoxExamples.fst)
    -e, --expr EXPR         Expression to evaluate (default: 'red (p3 ())')
    -o, --output FILE       Output AST file (default: output.ast)
    -t, --target TARGET     Peregrine target (ocaml|c|wasm|rust|elm) (default: ocaml)
    -v, --verbose           Enable verbose output
    --bypass-wf             Bypass wellformedness checks in peregrine
    -h, --help              Show this help message

EXAMPLES:
    $0                                          # Use defaults
    $0 -e 'red (p1 ())'                        # Test p1 example
    $0 -e 'red_prog nat_program' -t c         # Compile full program to C
    $0 --verbose                                # Show detailed output

EOF
    exit 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -f|--file)
            FSTAR_FILE="$2"
            shift 2
            ;;
        -e|--expr)
            EXPRESSION="$2"
            shift 2
            ;;
        -o|--output)
            OUTPUT_AST="$2"
            shift 2
            ;;
        -t|--target)
            PEREGRINE_TARGET="$2"
            shift 2
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        --bypass-wf)
            BYPASS_WF=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            echo -e "${RED}Error: Unknown option $1${NC}" >&2
            usage
            ;;
    esac
done

# Helper function for logging
log() {
    echo -e "${GREEN}[$(date +'%H:%M:%S')]${NC} $*"
}

error() {
    echo -e "${RED}[ERROR]${NC} $*" >&2
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $*" >&2
}

# Step 1: Compile the F* file and evaluate the expression
log "Step 1: Evaluating F* expression..."
log "  File: $FSTAR_FILE"
log "  Expression: $EXPRESSION"

if ! FSTAR_OUTPUT=$(./fstar-eval.py --lax "$FSTAR_FILE" "$EXPRESSION" 2>&1); then
    error "F* evaluation failed!"
    echo "$FSTAR_OUTPUT" >&2
    exit 1
fi

if [ "$VERBOSE" = true ]; then
    echo "$FSTAR_OUTPUT"
fi

# Extract the result (everything after the ↓ symbol)
# The result is a JSON-style quoted string, so we need to:
# 1. Extract the content after the ↓
# 2. Remove the outer quotes
# 3. Unescape the inner quotes (\" -> ")
AST_CONTENT=$(echo "$FSTAR_OUTPUT" | grep -oP '↓\s+\K.*' | sed 's/^"//;s/"$//' | sed 's/\\"/"/g')

if [ -z "$AST_CONTENT" ]; then
    error "Failed to extract AST from F* output"
    error "Output was: $FSTAR_OUTPUT"
    exit 1
fi

log "  ✓ F* evaluation successful"

# Step 2: Save the AST to file
log "Step 2: Saving AST to $OUTPUT_AST..."

# Check if this is a standalone term or a full program
# Peregrine expects a program which is a product (global_env, main_term)
# A program starts with ((( (three open parens for the env list)
# A standalone term starts with ( followed by a term constructor like (tCase, (tApp, etc.
if [[ "$AST_CONTENT" =~ ^\(t[A-Z] ]]; then
    log "  Detected standalone term, wrapping in minimal program..."
    # Create minimal program with just the base STLC environment
    BASE_ENV='((((MPfile ("STLC")) "unit") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "unit" false IntoAny ((constructor_body "tt" 0)) ()))))) (((MPfile ("STLC")) "bool") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "bool" false IntoAny ((constructor_body "true" 0) (constructor_body "false" 0)) ()))))) (((MPfile ("STLC")) "prod") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "prod" false IntoAny ((constructor_body "pair" 2)) ()))))) (((MPfile ("STLC")) "sum") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "sum" false IntoAny ((constructor_body "inl" 1) (constructor_body "inr" 1)) ()))))) (((MPfile ("STLC")) "nat") (InductiveDecl (mutual_inductive_body Finite 0 ((one_inductive_body "nat" false IntoAny ((constructor_body "zero" 0) (constructor_body "succ" 1)) ()))))))'
    AST_CONTENT="($BASE_ENV $AST_CONTENT)"
fi

printf '%s\n' "$AST_CONTENT" > "$OUTPUT_AST"
log "  ✓ AST saved ($(wc -c < "$OUTPUT_AST") bytes)"

if [ "$VERBOSE" = true ]; then
    echo "AST content:"
    cat "$OUTPUT_AST"
    echo ""
fi

# Step 3: Validate the AST with peregrine
log "Step 3: Validating AST with peregrine..."
VALIDATE_CMD="peregrine validate \"$OUTPUT_AST\""
if [ "$BYPASS_WF" = true ]; then
    VALIDATE_CMD="$VALIDATE_CMD --bypass-wf"
fi

if ! VALIDATE_OUTPUT=$(eval $VALIDATE_CMD 2>&1); then
    # If validation fails, show error but continue if bypass-wf is set
    if [ "$BYPASS_WF" = false ]; then
        error "Peregrine validation failed!"
        echo "$VALIDATE_OUTPUT" >&2
        exit 1
    else
        warn "Validation failed but continuing with --bypass-wf"
        if [ "$VERBOSE" = true ]; then
            echo "$VALIDATE_OUTPUT"
        fi
    fi
else
    log "  ✓ AST validation successful"
    if [ "$VERBOSE" = true ]; then
        echo "$VALIDATE_OUTPUT"
    fi
fi

# Step 4: Compile with peregrine to target language
log "Step 4: Compiling to $PEREGRINE_TARGET..."
OUTPUT_FILE="${OUTPUT_AST%.ast}.${PEREGRINE_TARGET}"

# Set appropriate file extension
case $PEREGRINE_TARGET in
    ocaml)
        OUTPUT_FILE="${OUTPUT_AST%.ast}.mlf"
        ;;
    c)
        OUTPUT_FILE="${OUTPUT_AST%.ast}.c"
        ;;
    wasm)
        OUTPUT_FILE="${OUTPUT_AST%.ast}.wasm"
        ;;
    rust)
        OUTPUT_FILE="${OUTPUT_AST%.ast}.rs"
        ;;
    elm)
        OUTPUT_FILE="${OUTPUT_AST%.ast}.elm"
        ;;
esac

COMPILE_CMD="peregrine \"$PEREGRINE_TARGET\" \"$OUTPUT_AST\" -o \"$OUTPUT_FILE\""
if [ "$BYPASS_WF" = true ]; then
    COMPILE_CMD="$COMPILE_CMD --bypass-wf"
fi

if ! COMPILE_OUTPUT=$(eval $COMPILE_CMD 2>&1); then
    error "Peregrine compilation to $PEREGRINE_TARGET failed!"
    echo "$COMPILE_OUTPUT" >&2
    exit 1
fi

log "  ✓ Compilation successful: $OUTPUT_FILE"
if [ "$VERBOSE" = true ]; then
    echo "$COMPILE_OUTPUT"
    echo ""
    echo "Generated file preview:"
    head -20 "$OUTPUT_FILE"
fi

# Success!
log "${GREEN}✓ All steps completed successfully!${NC}"
log "  F* file: $FSTAR_FILE"
log "  Expression: $EXPRESSION"
log "  AST file: $OUTPUT_AST"
log "  Output file: $OUTPUT_FILE"
