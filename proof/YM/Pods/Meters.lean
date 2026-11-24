import YM.Pods.Hoops
import YM.Pods.Typing
/-! admissible continuum-mesh pay for homogeneous point-calibrated lookups.
Includes derived interior-supported checker with same arity power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
-- keep scheduler later.H root sizes at j. up adjacent measure 
noncomputable def clock (i:ℕ):= Real.log ((S.spacing i)⁻¹)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
structure Sway :Prop where
    high : Tendsto (fun i => (S.step i).L.val) atTop atTop
    track (e:ℝ) : 0<e → ∀ᶠ i:ℕ in atTop, clock S (i+1) ≤ (1+e)*clock S i
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
noncomputable def rayM (d:ℕ)(e:ℝ)(v:ℝ)(i:ℕ):= v*Real.exp (((d:ℝ)/2+e)*clock S i)
local notation "V"=> rayM cK d e
set_option quotPrecheck false
abbrev bloke (S:Sequence)(P:Calibration S)(w:Label d)(v:ℝ)(j i:ℕ):Prop:= ∀ (h:j ≤ S.N i) (he:Even (S.S.side (S.R i) j).val) (x: Cover), let g:= viewW S.S (S.R i) h; let R:= (S.A i).regulator; floorL (mural g he (wrap _ x)) R.average R (P.physical none i w x) 0 ≤ v
abbrev bright (S:Sequence)(P:Calibration S)(w:Label d)(v:ℝ)(j):=∀ᶠ i in atTop,bloke S P w v j i
local notation "br"=> bright C Pκ
lemma signsFinite {i:List Axis→ ℝ→Prop}(h:∀ k,∃ A:ℝ,0≤A∧i k A) (he:∀ k A,∀ b≥A,i k A→ i k b)(z:ℕ):∃ A:ℝ,0 ≤ A ∧ ∀ l : List Axis, l.length≤ z→ i l A:=by choose A hA hz using h; obtain ⟨b,hb,hB⟩:= Hub.cloth A z; exact ⟨b,hb,fun l h=>he _ _ _ (hB _ h) (hz l)⟩
-- bounded length.C.N forall
lemma eraBound {P:Type*}{l:Filter P}{B:List Axis→P→Prop}(h:ℕ)(he:∀ i:List Axis,i.length ≤ h→∀ᶠ j in l, B i j): ∀ᶠ j in l,∀ i:List Axis,i.length≤ h→ B i j:=by
    induction h generalizing B with
    | zero=> filter_upwards [he [] (by simp)] with j hj i hp; rwa [(List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp))]
    | succ h ih=> filter_upwards [he [] (by simp),eventually_all.mpr (fun i:Axis=>ih (B:=fun k=> B (i :: k)) fun k hk=>he _ (by simp; omega))] with i hi H L hL; rcases L with _|⟨a,k⟩; exact hi; exact H a k (Nat.le_of_succ_le_succ hL)
lemma going {S:Sequence} (P:Calibration S){A B:ℝ}(w:Label d)(hk:A ≤ B){j:ℕ}(ht:bright S P w A j):bright S P w B j:=ht.mono fun i hx h he b=> (hx h he b).trans hk
include hY he hp hw
lemma riches :∃ v:ℝ, 0 ≤ v∧∀ᶠ j in atTop,∀ l:List Axis,l.length≤24→ bright C Pκ (spine sym w l) (V v j) j:=by
    let Q l:= spine sym w l
    have h(l): ∃ v:ℝ,0 ≤ v∧∀ᶠ j in atTop,br (Q l) (V v j) j:=by have hh:= toured sym w q hp l hw; exact (hY d (Q l) q).envelope hh.1 hh.2 he
    obtain ⟨v,hp,hh⟩:= signsFinite h (fun l A b hx hi=>hi.mono fun j hj=> going _ _ (show V A j ≤ V b j from mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)) hj) 24; exact ⟨v,hp,eraBound 24 hh⟩
variable (hs:Sway C.S)
local notation "R" i:arg => (C.A i).regulator
include hs
-- adjacent estimator.
lemma flavorT : ∃ v:ℝ,0 ≤v ∧∀ᶠ j in atTop,∀ᶠ i in atTop,∀ l:List Axis,l.length≤24→ bloke C Pκ (spine sym w l) (rayM C.S d e v j) (j+1) i:=by
     let a:= e/2; have ha:0<a:=half_pos he; let g:ℝ:=(d:ℝ)/2; let f:=g+a; have hf:0<f:= add_pos_of_nonneg_of_pos (by unfold g; positivity) ha; let b:=(e-a)/f; have hb:0 < b:=div_pos (sub_pos.mpr (half_lt_self he)) hf
     obtain ⟨v,hv,H⟩:= riches (C:=C) Ht Uv sym base U w q hp hw hY a ha
     refine ⟨v,hv,?_⟩; filter_upwards [(tendsto_add_atTop_nat 1).eventually H, hs.track _ hb] with j h hz
     refine eraBound 24 (fun l hl=> going _ _ ?_ (h l hl)); unfold rayM; apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_left hz hf.le).trans; apply le_of_eq; rw [← mul_assoc]; congr 1; change f * (1+b)=g+e; unfold b; field_simp; unfold f; ring
omit hY he hp hw hs
-- path support geometry
variable {β ν:ℝ}(hC:C.Path β ν)
include hC
lemma stamp_big (j:ℕ): Tendsto (fun i=> ratioTo (C.S) (C.N i) j) atTop atTop:=by
   let XY:= C.S.ratio; have hf: Tendsto (fun i=> (((XY (C.N i)).val :ℕ):ℝ)) atTop atTop:=by
       have he:= (tendsto_inv_nhdsGT_zero.comp hC.physical); exact he.congr (by intro i; simp [Scheme.spacing,XY])
   apply tendsto_atTop.2; intro k; filter_upwards [hf.eventually_ge_atTop ((XY j).val*(k:ℝ)),hC.uv.tendsto_atTop.eventually_ge_atTop j] with i hi hk; change k ≤ _; have h': (XY j).val*k ≤ (XY (C.N i)).val:=by exact_mod_cast hi
   rw [show (XY (C.N i)).val=_ from factorize hk] at h'; exact Nat.le_of_mul_le_mul_left h' (XY j).pos
lemma sideW (i m:ℕ) : 4 ≤ ((C.S).side (C.R i) m).val:=by rw [Scheme.side,PNat.mul_coe]; exact (hC.atLeast i).trans (le_mul_of_one_le_right (Nat.zero_le _) (C.S.ratio m).property)
open scoped ComplexOrder
lemma battery (i) : (R i).average 1=1:=by
   have h:= hC.normalized i; apply Regulator.average_one; have hf:= (h.normal (m:=C.N i) le_rfl).ne'; rw [h.start] at hf; change joint ⇑((R i).density*1) ≠0; rwa [mul_one] -- `(R i).` notation 
omit hC
lemma largeK (z:Finset Cover):∃ r:ℕ,∀ b∈z,∀ a:Axis,(b a).natAbs<r:=by
    classical
    exact ⟨ (∑ i∈z,∑ j:Axis,(i j).natAbs)+1,fun i hi j=> Nat.lt_succ_of_le ((Finset.single_le_sum (s:=univ) (f:=fun j:Axis=>(i j).natAbs) (by simp) (mem_univ j)).trans (Finset.single_le_sum (s:=z) (f:=fun i:Cover=> ∑ j:Axis,(i j).natAbs) (by simp) hi))⟩
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.flavorT
#print axioms YM.Massive.Patria.Hub.stamp_big
