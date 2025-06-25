Record PtsSig : Type :=
  mkPtsSig{
      St : Set;
      Ax : St -> St -> Set;
      Ru : St -> St -> St -> Set;
    }.
