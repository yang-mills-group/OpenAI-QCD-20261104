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
private theorem max_end (g : ℕ → ℝ) (m : ℕ) (hn : ∀ i, i ≤ m → 0 ≤ g i) (A : ℝ)
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
-- Bracket in Cover. bounds cite T state.M surrounding.i.P.Assign insect.Any p later via orientation.
lemma componentTip (x:ℕ→Per n)(d:ℕ)(h:∀ i,i+1≤ d→x (i+1)=x i+1)(b:ℤ)(j:ℕ)(hp:j≤d)(he:(b:Per n)=x j)(k:ℕ)(hk:k≤d): x k=((b+(k:ℤ)-j:ℤ):Per n):=by
   have hh(s) (hs:s≤d) : x s=x 0 + s:=by induction s with| zero=>simp|succ i ih=> rw [h i hs,ih (by omega)]; push_cast; abel
   rw [hh k hk]; push_cast; rw [he,hh j hp]; abel
variable (b:Cover) (V₀:ℝ)
variable (g:Ratio c n)(hG:Odd g.count.val)(hs:Even c.val)
include hu hG hs he hv hx hn hz
lemma upperBase (h:wrap n b∈ T.margin O (3*g.count.val)) (ht:∀ b:Cover,wrap n b∈T.margin O (2*g.count.val)→Base T O 0 (Q b)) (hp:∀ b:Cover, wrap n b∈ T.margin O (2*g.count.val)→ wrap n b∈Spiro.onCenters g hs (Spiro.homeFor g T)→Fχ (Q b) O ≤ V₀): Fχ (Q b) O ≤ V₀:=by
   choose v j hj hu' hr hs' ht' ha hb using fun i:Axis=> Spiro.bracket _ _ hs hG _ h i
   let Q'(x:Axis→ℕ): Cover:=fun i=> b i+x i-j i
   let B(x:Axis→ℕ): Site n:=fun i=>v i (x i) i
   let H:=g.count.val
   have hh : Q' j=b:= by funext; dsimp [Q']; abel
   have hp0(x:Axis→ℕ)(hx:∀ i,x i ≤H): wrap n (Q' x)=B x:=by
       funext i; apply Eq.symm; refine componentTip (fun k=>v i k i) H ?_ (b i) _ (hj i) ?_ _ (hx i)
       · intro l hh; rw [hs' i l hh]; simp
       rw [hu' i]; rfl
   have h₁ (x:Axis→ℕ)(hv:∀ i,x i≤ H) : wrap n (Q' x) ∈ T.margin 0 (2*H):=by rw [hp0 x hv]; exact ⟨fun i=>(hr i _ (hv i)).1 i,fun i=> (hr i _ (hv i)).2 i⟩
   have h₂ : ∀ i, j i ≤ H:= hj
   let Pχ (x:Axis→ℕ):= Fχ (V n (Q' x) w) O
   have hpW (D:Finset Axis)(z:Axis→ℕ)(h:z≤Function.const _ H)(ht₁:∀ i,i ∉ D→ z i=0∨ z i=H) : Pχ z ≤ V₀:=by
      induction D using Finset.induction_on generalizing z with
      | empty=>
          refine hp (Q' z) (h₁ z h) ((Spiro.belongs _ _ hs hG).mpr fun i=>?_); rw [hp0 z h]; change Spiro.OnGrid _ _ _ (v i (z i) i); rcases ht₁ i (by simp) with he|he <;> rw [he]; exacts [ha i,hb i]
      | insert a D ha ih=>
         let f(x:ℕ):=update z a x
         have hH (i:ℕ)(hi:i ≤ H):f i ≤ Function.const _ H:= by intro b; by_cases he:b=a; subst b; simpa [f, Function.const_apply] using hi; unfold f; rw [Function.update_of_ne he]; exact h _
         have hT (i:ℕ)(hi:i=0∨ i=H)(b:Axis)(hb: b∉D): f i b=0∨ f i b=H:=by
             by_cases he:b=a; subst b; simpa [f] using hi; unfold f; rw [Function.update_of_ne he]; exact ht₁ b (by simp [he,hb])
         have hm(i:ℕ):Q' (f (i+1))= Q' (f i)+Lattice.step a:=by funext x; by_cases hx:x=a <;> simp [Q',f, hx]; abel -- test
         let G(i):= Pχ (f i)
         have hr:= max_end G H (fun _ _=>floor_nn ..) V₀ (fun i hi=>?_) (ih _ (hH 0 (Nat.zero_le _)) (hT 0 (Or.inl rfl))) (ih _ (hH H le_rfl) (hT H (Or.inr rfl))) _ (show z a≤ H from h a)
         · change Pχ (f (z a))≤ _ at hr; unfold f at hr; rwa [Function.update_eq_self] at hr
         let p:=Q' (f (i+1)); let d:= (step a : Cover); have hq(i)(h:i ≤ H):= ht (Q' (f i)) (h₁ (f i) (hH i h))
         have hQ:Q' (f i)=p-d:=by unfold p d; rw [hm,add_sub_cancel_right]
         have hx' : Q' (f (i+2))=p+d:=hm (i+1); have hi' : i ≤ H:=by omega
         change Fχ (Q p) O ^2 ≤ Fχ (V n (Q' (f i)) w) O * Fχ (V n (Q' (f (i+2))) w) O; rw [hQ,hx']; apply rocking T a R V sym hz hv hx w q hu he hn p; exact hQ ▸ hq i hi'; exact hx' ▸ hq _ hi
   rw [← hh]; exact hpW _ _ (show j≤Function.const _ H from h₂) (show ∀ i,i∉(univ:Finset Axis)→ _ from fun i hi=>False.elim (hi (mem_univ i)))
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.upperBase
