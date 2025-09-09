--------------------------- MODULE ThemeCommon1 ------------------------------
EXTENDS Naturals, TLAPS
CONSTANTS Theme, Pack, PackVersion, PackTheme, InitialPack, NoPack, IsNewestOfItsTheme(_, _)
ASSUME Assumptions ==
  /\ Theme /= {}
  /\ Pack /= {}
  /\ PackVersion \in [Pack -> Nat]
  /\ PackTheme \in [Pack -> Theme]
  /\ InitialPack \in Pack
  /\ NoPack \notin Pack
  /\ \A pack \in Pack, packs \in SUBSET Pack :
       IsNewestOfItsTheme(pack, packs) =
         \A p \in packs:
           (PackTheme[p] = PackTheme[pack]) => (PackVersion[pack] >= PackVersion[p])
=============================================================================