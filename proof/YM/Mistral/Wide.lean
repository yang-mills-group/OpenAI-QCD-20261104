import YM.Mistral.Garb
import YM.Mistral.Site
/- center wallet receipts explicit for two through-q estimators: one angular off and one point canopy. Stress GreenP from generic. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub.Duon
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
open Needle Needle.GaugeP Hub Cells Massive.Romance
variable {C:Sequence} {S:Scheme}{N j k ℓ P :ℕ}(R:Side)(he:Even R.val) -- binder P
local notation "φ" => S.side R
local notation "Y" x:arg=>viewW S R x
variable (x:Site ((S.side R j)))
local notation "η" j:arg=> evenW S R he j
local notation "D"=> ratioTo S ℓ j
variable (hj:j≤ℓ)(hr:ℓ≤ N)
set_option quotPrecheck false
local notation "T₀"=> Column.sky S R j ℓ hj (evenW S R he j) (0:Site (φ ℓ))
local notation "Tz"=> Column.sky S R j N (hj.trans hr) (evenW S R he j) (0:Site (φ ℓ))
-- origin or aligned hdet.H priori support.Any orientation. projection.
include he hj
lemma opensM: (viewW S R hj).embed x ∈ (T₀).margin x (ratioTo S ℓ j/2):=by
    unfold Column.sky; rw [Column.homes,Intag.key_margin _ _ _ _ _ (viewOdd ..),zero_add,separation_self]; simp
-- T unaligned need margin.Step below.inner. condition
include hr
lemma opensP (b:Cover)(ht:(viewW S R hr).parent (wrap (φ N) b)=0)(hp: j+1 ≤ ℓ)(hX:20≤ (S.step j).L.val): wrap (S.side R N) b ∈ (Tz).margin (0:Site (S.side R j)) (3*ratioTo S N (j+1)):=by
     rw [Off.ruler (S:=S) hp hr]; let d:= ratioTo S ℓ (j+1); let q:= ratioTo S N ℓ
     have hV: 3*d+1 ≤ D/2:=by rw [step_factor hp]; have hv:d>0:=(odd_to (S:=S) hp).pos; have hC:= Nat.mul_le_mul_right d hX; change _≤ (_*d)/2; omega
     have hn: (0:Site (φ ℓ))∈ (T₀).margin (0:Site (φ j)) (3*d+1):=by
          have ht0: 0∈ (T₀).margin (0:Site (φ j)) (D/2):=by have hx:= opensM (S:=S) R he (0:Site (φ j)) hj; rw [show _=_ from (show (viewW S R hj).embed 0=0 from (Y hj).root.map_zero)] at hx; exact hx
          exact padding _ _ _ _ _ (viewOdd _ _ hj) ht0 hV
     rw [show 3*(_*ratioTo S ℓ (j+1))= q*(3*d) from by unfold q d; ring]
     apply smeared R he hj hr (3*d) 0 0; rw[ht]; exact hn
-- actual test displacement v through p.Observer.L. support crest shift. Need point nonzero at torus grid. scalar price entrance. 
variable {β ν:ℝ}(h:C.Path β ν)
include h
omit he hj hr
lemma wind {k:ℕ}(x: Cover)(hp:x≠0): ∀ᶠ i in atTop,(wrap (C.S.side (C.R i) k) x)≠0:=by
     have hx: ∀ᶠ i in atTop,2*(Laurent.size x)< (C.S.side (C.R i) k).val:=by apply h.infinite.eventually_gt_atTop (2*(Laurent.size x))|>.mono; intro i hi; rw [Scheme.side,PNat.mul_coe]; exact lt_of_lt_of_le hi (le_mul_of_one_le_right (Nat.zero_le _) (C.S.ratio k).pos)
     filter_upwards [hx] with i hi hu; apply hp; apply Eq.trans (FreeResolvent.size_centers _ _ le_rfl hi|>.symm); rw [hu]; ext; simp [lift] -- lift_zero simp.
end YM.Massive.Patria.Hub.Duon
#print axioms YM.Massive.Patria.Hub.Duon.opensP
