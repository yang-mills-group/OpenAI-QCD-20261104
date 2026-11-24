import YM.Patria.Sunrise
/-! A schedule API adaptable to tower of Cuts. For each loose rank. Public Beacon calibration before phase integration etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
namespace Depth
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
variable {S:Scheme}{r:Side}{N d i m M:ℕ}
variable (A:Run S N r 6)(H:SourceRead.TaperHol)
variable (B: Cover→ Label d→ Insertion (S.side r N) 6)
variable (u:Averaging)(b:Cover) (hA:A.Actual)
open Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Poised Poised.Plans.Stamp
-- useful for ranking stronger.U.Lo prices; input Travel across every i.
abbrev Market(S:Scheme)(r:Side)(d:ℕ):= ∀ m:ℕ,Cover→Label d→Bool→Density (S.side r m) 6→Prop
variable (W:Market S r d)
local notation "Sn" =>A.regulator.density
-- l physical cutoff, start all charges.M geometry constants 60.Moored names
open Plans Stative Plans.Orientation -- locate
structure Pilgrimage (T:ℕ) :Prop where
    boot (b:Cover)(x:Label d)(q:Bool): moored x.val q→ x≠0 → W N b x q (A.density N*⇑(B b x)) -- include
    furnished (b:Cover)(x:Label d)(q:Bool) (i:ℕ)(h0:T ≤ i) (h1:i ≤ N)(X:Density (S.side r i) 6) : W i b x q X → Tally H b x (A.density i) X
    rolling (b:Cover)(i:ℕ)(h0:T≤ i) (h1:i<N)(J:Type)[Fintype J][Nonempty J](p:J→ℝ)(F:J→Massive.Density (S.side r (i+1)) 6)(x:J→ Cover)(v:Label d)(q:Bool): v≠0→(∀ i,0 ≤ p i)→(∑ i,p i)=1 → (∀ j, let f:=stitch S r i; let R:=f.ratio; separation (R.parent (wrap _ (x j))) (wrap _ b) ≤60 ∧ Laurent.size (cellar R.count (x j)-b) ≤60) →(∀ j,W (i+1) (x j) v q (F j)) →∃ y: Label d,y≠0 ∧ W i b y q (∑ j,(p j:ℂ) • A.block i (F j))
    positions (b a:Cover)(x:Label d) : march a (B b x)=B (b+a) x
variable (h:Pilgrimage A H B W M)
local notation "Tr" L:arg =>trolley A (fun i=> B i L)
variable {q:Bool}
include h hA
lemma abundance (x:Label d)(hp:moored x.val q)(he:x≠0) (hc:i ≤ N)(hi:M ≤ i): ∃ y:Label d,y≠0 ∧ ∀ b, W i b y q ((Tr x) u i b):=by
    induction hc using Nat.decreasingInduction with
    | self=> refine ⟨x,he,fun b=>?_⟩; have h:=h.boot b x q hp he; rw [hA.start] at h; rw [boarding]; exact h
    |of_succ i hk ih=>
       let R:= (stitch S r i).ratio; obtain ⟨y,hp',hf⟩:= ih (by omega); obtain ⟨J,hJ,hN,p,t,hP,h0,hX,hQ⟩:=Rolls.constitution (X:=Insertion (S.side r N) 6) u R
       let x' (b:Cover) j:= R.count.val • b+t j
       let Y b j := (Tr x) u (i+1) (x' b j)
       have hF (b:Cover): ⇑((Tr x) u i b)=∑ j,(p j:ℂ) • A.block i (Y b j):= trailer A (fun b=>B b x) u b p t hk hQ
       choose Yv hv1 hv2 using fun b:Cover=> h.rolling b i hi hk J p (fun j=> Y b j) (x' b) y q hp' hP h0 (fun j=> hX j b) (fun j=> hf _) -- coerces?
       have hh(b:Cover): W i b (Yv b) q ((Tr x) u i b):= hF b |>.symm ▸ hv2 b
       refine ⟨Yv 0,hv1 _,fun b=>?_⟩
       have hb:= Canvas.moved H ((Tr x) u i 0) b 0 (h.furnished 0 _ _ i hi hk.le _ (hh 0)) (by rw [pier A hA hk.le]; exact first A _ hk.le b) -- hG
       rw [axial A hA (fun i=>B i x) u (fun b c=> h.positions b c x) b _ hk.le,zero_add] at hb
       rw [Canvas.consensus H b ((Tr x) u i b) hb (Yv b) (h.furnished b _ _ i hi hk.le _ (hh b))]; exact hh _
end Depth
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Depth.abundance
