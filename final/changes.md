# Strings in Racer

# String Representation
- SNAKEVAL strings are a special type of tagged tuples where the values in the tuple are 
  snake nums representing the first 7 ascii bits of the character (we don't support ascii > 127). 
- Since each character is between `0` and `2^7`, each character value is doubled to ensure
  it will be a valid snake num during garbage collection (since we do BFS GC). 
- For efficiency, each 8-byte offset in the string starting after the length
  contains 8 1-byte characters, filling the offset sequentially from start to end

# Tag Updates
- All tag masks except for numbers were extended from `0x7` to `0xf`
- The bool tag was updated from `0x7` to `0xf` 
- The string tag was added as `0x9`

# Expr Updates
- New `EStr` and `CStr` AST types were added to allow compiling strings
- New `IsStr` Prim1 type added to match other is<type> identifiers
- Conversion Prim1s were added to convert between Strings, numbers, and bools
- Convenience `Tuple` Prim1 added to easily create tuples of a given length initialized to 0
- String operation Prim2s added for `Concat`, `Split`, and `Join`
- split, join, and concat prim2s were added since they require extra arg passing than the native funs
- New `ESubstring` and `CSubstring` AST types added to allow string operations using Python substr syntax

# Lexer and Parser Updates
- Capability to parse string literals and herestrings
- Lex/Parse rules for the following exprs:
  - `isstr`
  - `tonum`
  - `tostr`
  - `tobool`
  - `split`
  - `join`
  - `tuple`
- Lex/Parse rules for `^` concat and `.` dot syntax

# Error Updates
- New compiler error for illegal characters in string literals
- New runtime errors:
  - `ERR_NOT_STR`
  - `ERR_INVALID_CONVERSION`
  - `ERR_SUBSTRING_NOT_NUM`
  - `ERR_SUBSTRING_OUT_OF_BOUNDS`
  - `ERR_LEN_NOT_TUPLE_NUM`
  - `ERR_INVALID_FORMAT_VALUES`
  - `ERR_INCORRECT_FORMAT_ARITY`
  - `ERR_TUPLE_CREATE_LEN`
  - `ERR_JOIN_NOT_TUPLE`
  - `ERR_JOIN_NOT_STR`
  - `ERR_SPLIT_NOT_STR`
  - `ERR_INVALID_CHAR`

# Runtime Updates
- GC updated to deeply copy strings
- Equality checks string contents
- printHelp prints string contents
- Errors with strings as the error values print string contents surrounded by quotes
- Input updated to return a SNAKEVAL string instead of an int or bool
- New functionality available in the language:
  - `len` for tuples and strings
  - `concat`
  - `substr`
  - `format`
  - `tuple`
  - `tobool`
  - `tostr`
  - `tonum`
  - `ascii_tuple_to_str`
  - `str_to_ascii_tuple`
  - `split`
  - `join`
  - `contains`
  - `get_ascii_char`

# Compile Updates
- `is_well_formed`:
  - String literals must have only ascii characters with values between 0 and 127
  - `format` is not checked for arity
- `desugar`:
  - `format` desugars its varargs into a single arg which is a tuple of tostring calls
- `c_call_arg_indirection` function:
  - A new function that changes the behavior of functions that will reserve heap space in the runtime
  - Instead of passing in all args normally, some are pushed to the stack, and the stack location is passed
    in instead
  - This allows us to know the location of a heap-allocated value after a possible gc pass when
    reserving memory
