import YM.Kai.Charon
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Massive.Run S n R 6)
open Cells YM.Intag.Pilgrim YM.Intag.Hymnal YM.Intag.Hickory
variable (r:Slate)(T:Tiling c)(a b:T.Cell)
noncomputable def rose (r: Slate) (q:List Axis): Slate:= match q with
   | .nil=>r
   | .cons i s=>opposed (rose r s) i
noncomputable abbrev charts:= rose r (reversa T a b)
lemma twists(h:b≠a): charts r T a b=opposed (charts r T a (YM.Intag.Pilgrim.μ T a b)) (post T a b).2:=by unfold charts; rw [writes T a b h,rose]
lemma stamp0 : charts r T a a=r:=by unfold charts reversa; rw[YM.Intag.Pilgrim.at_p]; rfl
end YM.Massive.PCAC.Oren
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace CardsT
open Pilgrim Tess Column Finset Plum UV
variable {S:Scheme}{R:Side}{k i ℓ p n:ℕ}(A:Massive.Run S n R 6)
local notation "Pr"=> Site (S.side R p)
variable (z:Site (S.side R ℓ))(hj:p ≤ ℓ)(hp:Even R.val)(P:Site (S.side R p))(x:Cover)
set_option quotPrecheck false
local notation "T"=> mural (viewW S R hj) (evenW S R hp p) z
local notation "X" => Pilgrim.bout T P rfl x
local notation "uP" j:arg=> μ T P j
local notation "κ" t:arg=> (mural (viewW S R hj) (evenW S R hp p) z).bandCut (post (mural (viewW S R hj) (evenW S R hp p) z) P t).1 (post (mural (viewW S R hj) (evenW S R hp p) z) P t).2
variable (U:Averaging)(Wq:Site (S.side R p) → Cover → Insertion (S.side R i) 6)
open Massive.Patria
local notation "Δq" u:arg=> tentT A U (Wq u)
open Poised Poised.Plans Poised.Display
variable {V0: YM.Source.Hol su}(A0: Lining.Temper.Collage.Exhibit V0)(η₀:SourceRead.TaperHol)(sy:RawSym) (d:ℕ)(pB: Site (S.side R p) → UV.Label d)(t:ℕ) (Q:PatchMix d) (hO: OrderMix A η₀ sy (Massive.Patria.Depth.Bloom A0 d) (i:=t) Q)
local notation "Qb"=>Massive.Patria.Depth.Bloom A0 d
local notation "Yq"=> fun (j:Pr)(b:Cover)=> Massive.Patria.Depth.Bloom A0 d (S.side R n) b (Q U (pB j))
variable (hR:Rubric sy (Massive.Patria.Depth.Bloom A0 d))(hA:A.Actual) (σ:Site (S.side R p)→Bool)(hi:ℓ≤ i)(ht:t≤ ℓ)(hv:i≤ n)
-- y normalized *before conversion to engineering real factors*. can scale norm power later.Mon.Transmission.M.
local notation "T★"=> Column.sky S R p n (hj.trans (hi.trans hv)) (evenW S R hp p) z
open PCAC
variable (Qz: PCAC.Oren.Slate)
local notation "Rh" j:arg=> PCAC.Oren.charts Qz T P j
local notation "Ink" j:arg=> PCAC.Oren.inkC (Rh j) A (i:=i) -- order?
local notation "Xt" j:arg=> report A (PCAC.Oren.inkC (Rh j) A (i:=i)) U
include hA hv
lemma speaksT (v:Pr)(g:v≠P)(b:Cover): Cylinder.Action.adj (κ v).pos (⇑(PCAC.Oren.inkC (Rh (uP v)) A (i:=i) b))=⇑(PCAC.Oren.inkC (Rh v) A (i:=i) ((κ v).flip.act b)):=by
      rw [PCAC.Oren.twists Qz T P v g]; exact PCAC.Oren.frolic _ A hA b _ hv
variable (Mm:Market S R d)(hMm:Wager A η₀ (Massive.Patria.Depth.Bloom A0 d) Mm t)
-- ctor all != by Forester
include hA hv hMm hR ht hi
local notation "Pζ" j:arg=> pB j
lemma phosphorsT (v:Pr)(h: Pζ P ≠0) (hX:∀ j,Tally η₀ 0 (pB j) (A.density t) ((Xt j) t 0)) : pB v≠0:=by
     suffices H:∀ n₀:ℕ,∀ v:Pr,(crestT T P v).length=n₀→ pB v ≠0 from H _ v rfl
     intro u; induction u with
     | zero=> intro v he; by_contra hh; have ht:v≠P:=by intro hk; subst v; contradiction
              rw [away_p T P ht] at he; cases he
     | succ n ih=>
        intro j he; by_cases hu:j=P; · rw [hu]; exact h
        have hv':= hX j; let a:= (κ j).pos; have hp2:= resolveR A hA hv (ht.trans hi) a U (PCAC.Oren.inkC (Rh (uP j)) A (i:=i)) (PCAC.Oren.inkC (Rh j) A (i:=i)) (speaksT A z hj hp P hA hv Qz j hu) (pB (uP j)) η₀ (Qb) sy hR Mm hMm (hX (uP j))
        rw [Canvas.consensus η₀ 0 _ hv' _ hp2]; have hx: (crestT T P (uP j)).length=n:=by rw [away_p T P hu,List.length_cons] at he; exact Nat.succ_injective he
        rw [LinearEquiv.map_ne_zero_iff]; exact ih (uP j) hx
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.phosphorsT
