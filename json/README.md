# json

JSON for Bend: `parse.bend` (text to `Maybe<Json>`), `print.bend` (compact
text), `value.bend` (the type, builders `obj` `arr` `num`, and path accessors
`get` `str_or` `u32_or` that read a missing key or a wrong kind as a default).

The lexer and the parser are tail-recursive state machines, one char and one
token per step over an explicit stack: no fuel, no recursion on the value, and
both compile to loops. Arrays and objects keep their cells inside the type
(`JCons`, `JPair`, `JNil`) instead of in a `List`, because Bend's termination
checker wants one argument that shrinks on every self-call; a rose tree over
`List<Json>` would need fuel everywhere.

Numbers keep their source text (`JNum{raw}`), so printing loses nothing.
Commas and colons are not policed; nesting, string ends and a single root are.
