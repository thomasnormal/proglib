# Interface instance and port connection wall

This parser-native fixture records the canonical-E boundary for IEEE
1800-2023 §§23.2.2 and 23.3. The ordinary census retains the exact generic
refusals for `InstanceSymbol:interface`, `PortConnection:InterfacePortSymbol`,
and the interface instance at `PDesign.instantiateE2`; the source assignment's
interface member target is a separate `AssignmentExpression:target` boundary.
The E state has no resolved interface-net/port driver relation, so these forms
remain loud rather than being flattened into scalar wires. Xcelium
24.03-s004 supplies four x/z rows; Icarus 13.0 rejects interface ports during
compilation, so no Icarus oracle result is claimed.
