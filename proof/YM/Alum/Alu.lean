import YM.Alum.Arbor
import YM.Pods.Shifts
import YM.Pods.Pivot
/-! Interpolate any off-centered register. req rooted bracket only. Same grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess Chess.Fortuna
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry
variable {c f m n:Side}{k d:ℕ}{F:ℕ}(T:Tiling n) (s:T.Cell)(i:Axis)
-- centered 0. all cover.Interp.V cost input h.A. BP
private theorem starrier (g : ℕ → ℝ) (m : ℕ) (hn : ∀ i, i ≤ m → 0 ≤ g i) (A : ℝ)
    (H : ∀ i, i+2 ≤ m → g (i+1)^2 ≤ g i*g (i+2)) (h : g 0 ≤ A) (he : g m≤A) : ∀ i ≤ m, g i ≤ A := by
  -- strict increase propagates
  have hv i (hp : i+1 ≤ m) (hr : g i < g (i+1)) : g (i+1) ≤ A := by
    have he_idx (p : ℕ) (hr' : g p<g (p+1)) (hs : p+2≤ m) : g (p+1)<g (p+2) := by
      have hl := H p hs
      have ha := hn p (by omega)
      have hh := hn (p+2) hs
      by_contra! hv
      apply (not_le.mpr ?_ hl)
      calc _ ≤ g p * g (p+1) := by gcongr
           _ < _ := by nlinarith
    have ht (q : ℕ) (hq : i≤q) (hz : q+1≤ m) : g q<g (q+1) ∧ g (i+1) ≤ g (q+1) := by
      induction q, hq using Nat.le_induction with
      | base => exact ⟨hr,le_rfl⟩
      | succ n hn ih => exact ⟨he_idx _ (ih (by omega)).1 hz,(ih (by omega)).2.trans (he_idx _ (ih (by omega)).1 hz).le⟩
    have hs : g (i+1) ≤ g ((m-1)+1) := (ht _ (by omega) (by omega)).2
    rw [show m-1+1=m by omega] at hs; exact hs.trans he
  intro i hi; induction i with
  | zero => exact h
  | succ i ih => exact le_or_gt (g (i+1)) (g i) |>.elim (fun h => h.trans (ih (by omega))) (fun h => hv i hi h)
/- reconstruct mesh covering by stencil interior. exact support at arbitrary lengths.P. sign interpolation saves nearby alignment test.All slots at integer AP. -/
variable (R:Regulator n 6)(V:Bore d)(sym:RawSym)(hz:Rubric sym V)(hv:T.kind=.link)(hx:R.t=0) (w:Label d)(q:Bool)(hu:moored w.val q)
variable (he:0 ≤ R.β)(hn:4 ≤ n.val)
local notation "Q" b:arg => V n b w
local notation "Δ"=> (step i : Cover)
local notation "Fχ"=> floorL T R.average R
local notation "Ψ" j:arg => T.copyMap j
local notation "θ"=> T.omega
local notation "Lv"=> replicateR T R
local notation "μ"=> R.average
local notation "O"=> (0:T.Cell)
variable (b:Cover) (H V₀:ℝ) (m:ℕ)(hm:0< m)
include hm
lemma patches (x:ℤ):∃ u:ℤ,∃ i:ℕ, i≤ m ∧ x=m*u+i:=by
     let u:= x/(m:ℤ); let i:= x%(m:ℤ); have hp:0 ≤ i:= Int.emod_nonneg _ (by exact_mod_cast hm.ne'); have he :i <(m:ℤ):= Int.emod_lt_of_pos _ (by exact_mod_cast hm); refine ⟨u,i.toNat,(by omega),?_⟩; rw [Int.toNat_of_nonneg hp]; exact (Int.mul_ediv_add_emod x _).symm -- include hm
include hv hu he hz hn hx hm
lemma strictH (h:wrap n b ∈ T.margin 0 (m+1+k)) (hp:∀ x:Cover,wrap n x ∈ T.margin 0 k→ Base T 0 0 (V n x w)) (hQ:∀ x:Cover, wrap n (m • x)∈T.margin 0 k → Fχ (Q (m • x)) 0 ≤ V₀) : Fχ (Q b) 0 ≤ V₀:=by
      choose p j hL hP using fun i:Axis=>patches m hm (b i)
      let u:=m • p; let Q'(x:Axis→ℕ): Cover:=fun i=> u i+x i
      have ht: b=Q' j:=funext fun i=>by simpa [u,Q'] using hP i
      have h₁(x:Axis→ℕ)(hz:∀ a, x a≤ m): wrap n (Q' x) ∈ T.margin 0 k:=by
          let z : Cover:=fun i=>(x i:ℤ)-(j i:ℤ); have hc: Q' x=z+b:=by rw[ht]; funext i; change u i+(x i:ℤ)=_+(u i+j i); unfold z; abel
          rw[hc,map_add]; exact marginB T h (z:=z) fun i=>by have ht:= hL i; have hs:=hz i; unfold z; omega
      have h₂ (x:Axis→ℕ)(ht:∀ a,x a=0∨x a=m):∃ z:Cover, Q' x=m • z:=by
              let z : Cover:=fun i=> if x i=0 then p i else p i+1
              refine ⟨z,funext fun i=>?_⟩; rcases ht i with h|h
              · simp [h,Q',z,u]
              have hv:x i≠0:= h.symm ▸ hm.ne'; simp [Q',u,h,z,hv,hm.ne']; ring -- may no goals.
      let Qχ (x:Axis→ℕ):= Fχ (V n (Q' x) w) O
      have hpW (D:Finset Axis)(z:Axis→ℕ)(h:z≤Function.const _ m)(ht₁:∀ i,i ∉ D→ z i=0∨ z i=m) : Qχ z ≤ V₀:=by
        induction D using Finset.induction_on generalizing z with
        | empty=> obtain ⟨x,hz⟩:=h₂ z fun i=>ht₁ i (by simp); apply le_trans (le_of_eq (show Qχ z =_ from (congr_arg (fun i=> floorL T R.average R (V n i w) O) hz))) (hQ x (hz ▸ h₁ z h))
        | insert a D ha ih=>
         let f(x:ℕ):=update z a x
         have hH (i:ℕ)(hi:i ≤ m):f i ≤ Function.const _ m:= by intro b; by_cases he:b=a; subst b; simpa [f, Function.const_apply] using hi; unfold f; rw [Function.update_of_ne he]; exact h _
         have hT (i:ℕ)(hi:i=0∨ i=m)(b:Axis)(hb: b∉D): f i b=0∨ f i b=m:=by
             by_cases he:b=a; subst b; simpa [f] using hi; unfold f; rw [Function.update_of_ne he]; exact ht₁ b (by simp [he,hb])
         have hm(i:ℕ):Q' (f (i+1))= Q' (f i)+Lattice.step a:=by funext x; by_cases hx:x=a <;> simp [Q',f, hx]; abel -- test
         let G(i):= Qχ (f i)
         have hr:= starrier G m (fun _ _=>floor_nn ..) V₀ (fun i hi=>?_) (ih _ (hH 0 (Nat.zero_le _)) (hT 0 (Or.inl rfl))) (ih _ (hH m le_rfl) (hT m (Or.inr rfl))) _ (show z a≤ m from h a)
         · change Qχ (f (z a))≤ _ at hr; unfold f at hr; rwa [Function.update_eq_self] at hr
         let p:=Q' (f (i+1)); let d:= (step a : Cover); have hq(i)(h:i ≤ m):= hp (Q' (f i)) (h₁ (f i) (hH i h))
         have h_Q:Q' (f i)=p-d:=by unfold p d; rw [hm,add_sub_cancel_right]
         have hx' : Q' (f (i+2))=p+d:=hm (i+1); have hi' : i ≤ m:=by omega
         change Fχ (Q p) O ^2 ≤ Fχ (V n (Q' (f i)) w) O * Fχ (V n (Q' (f (i+2))) w) O; rw [h_Q,hx']; apply rocking T a R V sym hz hv hx w q hu he hn p; exact h_Q ▸ hq i hi'; exact hx' ▸ hq _ hi
      rw [ht]; exact hpW _ _ (show j≤Function.const _ m from hL) (show ∀ i,i∉(univ:Finset Axis)→ _ from fun i hi=>False.elim (hi (mem_univ i)))
omit hv hu he hz hn hx hm
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.strictH
