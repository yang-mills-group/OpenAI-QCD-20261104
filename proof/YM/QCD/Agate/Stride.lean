import YM.QCD.Agate.Sire
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D S:Lot}
open Tide Flume YM.Next.Free Kites
open Acre.Rails.IV Land.Wall
variable (W: Wall)(h:W.Within D S)
lemma feast (x:Paper D F)(s:ℕ→Side)(hv:Tendsto (fun i=> (s i).val) atTop atTop)(hk:∀ i,Even (s i).val):∀ᶠ k in atTop, tallH (FaceR W (hk k)) (jewel (origin (s k)) x)= jewel (origin (s k)) (flash W h x):=by
    have he(D:Lot):∀ᶠ k in atTop,∀ i:Court D,(Tide.simple (FaceR W (hk k))).stamp (leap (origin (s k)) i.val)=chrom W:= eventually_all.mpr (fun i=> stumpy W s hv hk i.val)
    filter_upwards [he D,he S] with k hp ht; rw [scenery W (hk k) h]; exact funext fun i=> twin W (hk k) h (x (crest (origin (s k)) ((FaceR W (hk k)).pullC su i))) hp ht
lemma reliable (x:Malt D F): flash W h x.val∈ political S F:=by
    let s (k:ℕ):Side:=⟨2*(k+1),by change 0<2*(k+1); omega⟩; have hv: Tendsto (fun i=>(s i).val) atTop atTop:=Filter.tendsto_atTop_mono' atTop ((Eventually.of_forall fun k=> (show id k≤ 2*(k+1) by simp; omega))) tendsto_id
    have hk(k:ℕ): Even (s k).val:=⟨k+1,(by change 2*(k+1)=_; omega)⟩
    obtain ⟨k,hl,hp⟩:= ((gravity S s hv).and (feast W h x.val s hv hk)).exists; apply stateG (origin (s k)) hl
    · rw [← hp]; exact tallCost _ (stageJ _ _ (staysP x))
    rw [← hp]; exact coated _ _ (floods _ (coated _ _ (jewelN _ x)))
noncomputable def torch (x:Malt D F): Malt S F:= ⟨flash W h x.val,reliable W h x⟩
lemma trusted(x:Malt D F)(s:ℕ→Side)(hv:Tendsto (fun i=> (s i).val) atTop atTop)(hk:∀ i,Even (s i).val):∀ᶠ k in atTop, tallH (FaceR W (hk k)) (visit (origin (s k)) x)= visit (origin (s k)) (torch W h x):=feast W h x.val s hv hk
end YM.QCD.Agate
