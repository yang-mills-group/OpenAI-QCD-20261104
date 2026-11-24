import YM.Rill.Leap
/-! Positivity of the full pre-Gram matrix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip Petals Finset
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q)(a:Axis) {β e:ℝ}(hp:C.Path β e)
set_option quotPrecheck false
local notation "Pₑ" i:arg=> evenW C.S (C.R i) (hp.even i) (C.N i)
local notation "C₀" i:arg=> panH (Pₑ i) a
local notation "W" i:arg=> (C.A i).regulator
namespace Strip
variable (u:Averaging)
noncomputable abbrev lyric (l:List (Petal P))(φ:ℕ→ℕ) (i:ℕ):=(l.map fun j=>signalW u j φ i).prod
variable (v: List (Petal P))(w: List (Petal P))(H:Q.Harmony P φ)
include hQ hp hφ
lemma bouquetR :∀ᶠ i in atTop, picture (C₀ (φ i)) (W (φ i)).zeroCut (lyric u v φ i)= lyric u (v.reverse.map (reflection P a)) φ i:=by
      induction v with |nil=> exact Eventually.of_forall (fun _=>pic_one) | cons b v ih=> filter_upwards [ih,rayT hQ hφ a hp b u] with i hi hh; unfold lyric at hi ⊢; simp only[List.reverse_cons,List.map_cons,List.map_nil,List.map_append,List.prod_append,List.prod_cons,List.prod_nil,pic_mul]; rw[hi,hh,mul_one]
include H
lemma speech (hv:Sunny (petals Q u v) a)(hx:Sunny (petals Q u w) a)(hw:∀ p∈v,Atlas C P φ p)(hy:∀ p∈w, Atlas C P φ p): Tendsto (fun i=> (W (φ i)).average (picture (C₀ (φ i)) (W (φ i)).zeroCut (lyric u v φ i)* lyric u w φ i)) atTop (𝓝 (tone (oppositeS L a (petals Q u v)++ petals Q u w))):=by
      let Q':= v.reverse.map (reflection P a) ++ w; have hP:petals Q u Q'=oppositeS L a (petals Q u v)++petals Q u w:=by unfold petals Q'; rw[List.map_append]; congr 1; exact moveT _ _ _ _
      have he: distinct (petals Q u Q'):=by rw [hP]; exact aheadV L a _ _ hv hx
      have H':∀ p∈Q',Atlas C P φ p:=by
          intro p h; rcases List.mem_append.mp h with hl|hl
          · obtain ⟨x,hx,rfl⟩:= List.mem_map.mp hl; exact thrum hφ a hp _ (hw _ (List.mem_reverse.mp hx))
          exact hy p hl
      have hz:= reaches H Q' u he H'; rw [hP] at hz; refine hz.congr' ( (bouquetR hQ hφ a hp u v).mono fun i hi=>?_ ); dsimp only; rw [hi]; unfold Q' lyric; rw [List.map_append,List.prod_append]
omit H hQ
include hp
lemma solar (G:∀ d,Cottage P d)(hS:Sway C.S) (hv:Sunny (petals Q u v) a)(hw:∀ p∈v, Atlas C P φ p): ∀ᶠ i in atTop,Fence (C₀ (φ i)).sector (lyric u v φ i):=by
      have hh(p:Petal P)(h:p∈v):0<p.x a:= hv.2 (sight u Q p) (List.mem_map_of_mem (f:=sight u Q) h)
      clear hv
      induction v with
      | nil=> exact Eventually.of_forall fun _=> Fence.one
      | cons p v ih=>
        have hk:= ih (fun i hi=>hw i (List.mem_cons_of_mem _ hi)) (fun i hi=>hh i (List.mem_cons_of_mem _ hi)); have hc:p∈p::v:= List.mem_cons_self; filter_upwards [hk,esteemed a G hp hS hφ p u (hw p hc) (hh p hc)] with i hi hz; exact hz.mult hi
end Strip
variable {N n:ℕ}
lemma matrixP {N:Side} (K: Cells.Cut N)(R: Regulator N 6) (hr:0 ≤ R.β)(h:R.Z≠0)(hh: 2 ≤ K.half.val)(hx:K.kind=.link)(u:Fin n→Insertion N 6)(H:∀ i,Fence K.sector ⇑(u i))(z:Fin n→ℂ): 0 ≤ ∑ i,∑ j,star (z i)*R.average (picture K R.zeroCut (u i)*u j)*z j:=by
    let f(i):= z i • u i; let F:= ∑ i,f i; let Wz x:= picture K R.zeroCut x
    have Hp:Fence K.sector F:= summedF f univ K.sector fun i _=> (H i).mass _
    have hL:0 ≤ R.average (Wz F* F):=mul_nonneg (show 0≤R.Z⁻¹ from inv_nonneg.mpr (Regulator.Z_nonneg hx hr hh)) (show 0 ≤ R.raw (picture K R.zeroCut F*F) from Regulator.signed hx hr hh _ Hp)
    have he:Wz F=∑ i, star (z i) • Wz (u i):=by
         suffices he:∀ S:Finset (Fin n), Wz (∑ i∈S,f i)=∑ i∈S, star (z i) • Wz (u i) from he univ
         intro S; induction S using Finset.induction_on with
         | empty=> simp only [sum_empty]; rw [show Wz 0=_ from (?_ : Wz 0=0)]; rw[← zero_smul ℂ (0:Insertion N 6),show Wz ((0:ℂ) • 0)=_ from pic_smul ..]; simp
         | insert i S hi ih=> rw [sum_insert hi,sum_insert hi,show Wz (f i +_)=_ from pic_add ..]; exact congr_arg₂ (HAdd.hAdd) (pic_smul ..) ih
    refine hL.trans_eq ?_; rw [he]; unfold F f; rw [Finset.sum_mul,map_sum]; refine sum_congr rfl fun i _=>?_; rw [mul_sum,map_sum]; refine sum_congr rfl fun j _=>?_ ; rw [smul_mul_assoc,mul_smul_comm,map_smul,map_smul]; simp only[smul_eq_mul,Wz]; ring
variable (G:∀ d,Cottage P d)(hr:Sway C.S)(H:Q.Harmony P φ)
include G hr H hφ hQ hp
lemma rpTrue (v:Fin n→Strip Q)(hv:∀ i,Sunny (v i) a)(z:Fin n→ℂ):0 ≤ crestG L a n v z:=by
     choose p hp' he using fun i=> Petals.seeks hp H hφ (v i) none
     have hv(i): Sunny (petals Q none (p i)) a:=(hp' i).symm ▸ hv i
     let A(i k:Fin n) (j:ℕ):= (W (φ j)).average (picture (C₀ (φ j)) (W (φ j)).zeroCut (lyric none (p i) φ j)*(lyric none (p k) φ j)); let B(j:ℕ):= ∑ i: Fin n, ∑ k:Fin n, (star (z i))*A i k j*z k; have hx(i k):Tendsto (A i k) atTop (𝓝 (tone (oppositeS L a (v i)++ v k))):=by have h:= speech hQ hφ L a hp none (p i) (p k) H (hv i) (hv k) (he i) (he k); rw [hp',hp'] at h; exact h
     have ht:Tendsto B atTop (𝓝 (crestG L a n v z)):= tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ fun k _=> ((hx i k).const_mul _).mul_const _)
     apply ge_of_tendsto ht; filter_upwards [eventually_all.mpr (fun i=> solar hφ a hp _ (p i) G hr (hv i) (he i))] with i hi; let k:=φ i; let R:= W k; let X:= C₀ k; have hL:4 ≤ (C.S.side (C.R k) (C.N k)).val:= sideW hp _ _; have hs:2 ≤ X.half.val:=by have h:= X.even; omega
     exact matrixP X R ((hp.normalized _).beta_pos (Nat.le_refl _) |>.le) (engaged hp k) hs rfl (fun j=> lyric none (p j) φ i) hi z
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.rpTrue
