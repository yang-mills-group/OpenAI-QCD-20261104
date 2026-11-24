import YM.Rill.Shin
/-! Direct symmetric strip powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip Petals Finset
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q)(a:Axis) {β e:ℝ}(hp:C.Path β e)
variable {n m:ℕ}
namespace Strip
variable (G:∀ d,Cottage P d)(hr:Sway C.S)(H:Q.Harmony P φ)
variable {v:Strip Q}{x:Strip Q}
-- General power inequality for symmetric iterates of Gram.
include hQ hp H hφ G hr
variable {Y:Strip Q→Strip Q} (hy:∀ v,Sunny v a→ Sunny (Y v) a)(hq:∀ v x,Sunny v a→ Sunny x a→ reach L a (Y v) x= reach L a v (Y x))
variable {F:Fin n→ Strip Q}(hF:∀ i,Sunny (F i) a)
local notation "y" j:arg=> Y^[j]
omit hQ hp H hφ G hr hq hF in
include hy in
lemma visiting (t:ℕ) : Sunny v a→Sunny (Y^[t] v) a:=by
    intro h; induction t with|zero=>exact h| succ t ih=> rw[Function.iterate_succ_apply']; exact hy _ ih
omit hQ hp H hφ G hr in
include hy hq hF in
lemma travels (p t:ℕ)(z:Fin n→ℂ): valley L a (y t∘F) (y p∘F) z z= valley L a F (y (t+p)∘F) z z:=by
     unfold valley; congr 1; apply funext; intro i; refine sum_congr rfl fun j _=>?_
     suffices h:∀ (t p:ℕ), reach L a (Y^[t] (F i)) (Y^[p] (F j))= reach L a (F i) (Y^[t+p] (F j)) by rw [comp_apply,comp_apply,comp_apply,h]
     intro t; induction t with
     |zero=> simp
     |succ t ih=> intro p; rw[Function.iterate_succ_apply',hq _ _ (visiting a hy _ (hF i)) (visiting a hy _ (hF _)),← Function.iterate_succ_apply' Y,ih]; rw [Nat.succ_add,Nat.add_succ]
omit hQ hp H hφ G hr
private lemma ruleReal (f:ℕ→ℝ) (B C:ℝ)(h:0 ≤ C)(hb:0 < B)(hx:∀ i,0 ≤ f i)(hr:∀ i, (f i)^2 ≤ f 0 * f (i+i))(hT:∀ i, f i ≤ C * B^i): f 1 ≤ B*f 0:=by
    by_cases hz:f 0=0; · rw [hz,mul_zero]; have h:= hr 1; rw [hz,zero_mul] at h; nlinarith only [h]
    have hs:0<f 0:= lt_of_le_of_ne (hx 0) (Ne.symm hz); let k:= f 1 / (f 0*B)
    by_contra! H; have hG:1 < k:= by unfold k; rw [one_lt_div (mul_pos hs hb),mul_comm]; exact H -- name
    have hV(i:ℕ): k^(2^i) ≤ f (2^i)/(f 0*B^(2^i)):=by
        induction i with
        | zero=> simp only [pow_zero,pow_one,k,le_refl]
        | succ i ih=>
          let v:ℕ:=2^i; let A:= f 0*B^v; have ht:0 < A:=mul_pos hs (pow_pos hb _); have Hf: v+v= 2^(i+1):=by rw [pow_succ]; unfold v; ring
          rw [←Hf,pow_add,pow_add]; refine (mul_self_le_mul_self (pow_nonneg (zero_le_one.trans hG.le) (2^i)) ih).trans ?_; change f v/A* (f v/A) ≤ f (v+v)/(f 0*(B^v*B^v)); rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos ht ht) (by positivity)]; have hg:= mul_le_mul_of_nonneg_right (hr v) (show 0≤ A* B^v by positivity); unfold A at *; nlinarith only [hg]
    have ht(i:ℕ): k^(2^i) ≤ C/(f 0):= (hV i).trans (le_trans (div_le_div_of_nonneg_right (hT _) (by positivity)) (by
          rw [div_le_div_iff₀ (by positivity) hs]; exact le_of_eq (by ring)))
    have hu:Tendsto (fun i:ℕ=> (2:ℕ)^i) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨i,h⟩:= (((tendsto_pow_atTop_atTop_of_one_lt hG).comp hu).eventually (eventually_gt_atTop (C/(f 0)))).exists; exact h.not_ge (ht i)
include hQ hp H hφ G hr hF hy hq
lemma symmetry (z:Fin n→ℂ) {C' B:ℝ}(h: 0 ≤ C')(hb:0 < B) (hu:∀ i:ℕ, ‖valley L a F (Y^[i]∘F) z z‖≤ C' * B^i): ‖valley L a F (Y ∘F) z z‖ ≤ B * ‖crestG L a n F z‖:=by
     let f(i):= ‖valley L a F (Y^[i]∘F) z z‖; change _ ≤ B*‖valley L a F F z z‖; rw [show Y=Y^[1] from (Function.iterate_one _).symm]; -- loops only lhs
     exact ruleReal f B C' h hb (fun _=> norm_nonneg _) (fun i=> by
          change ‖valley L a F _ z z‖^2≤ ‖valley L a F F z z‖ * ‖valley L a F (Y^[i+i] ∘ F) z z‖; rw [← travels L a hy hq hF]; exact lights hQ hφ L a hp G hr H F _ z z hF (fun j=>visiting a hy i (hF j))) hu -- order hQ?
end Strip
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Strip.symmetry
