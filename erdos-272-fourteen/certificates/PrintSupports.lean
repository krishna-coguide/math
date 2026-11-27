import Erdos272.KernelSupports

def main : IO Unit :=
  IO.println (reprStr (E272.Neutral.kernelSupports.map (·.map BitVec.toNat)))
