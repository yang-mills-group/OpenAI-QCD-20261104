import YM.Massive.Ribbon.Ball
import YM.Work.G01
import YM.Work.G02
import YM.Work.G03
import YM.Work.G04
import YM.Work.G05
import YM.Work.G06.Formula
/-! # Response germs for exact stencil synthesis (real jets).

Work at unweighted polynomial level. `Response` uses twice-engineering order at
h=0, in particular includes order zero even when testing filtration 0. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus
open Lattice Wilson RG Source Function QCD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
variable {E F V E' A : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E'][NormedSpace ℝ E']
  [NormedAddCommGroup V][NormedSpace ℝ V][NormedRing A][NormedAlgebra ℝ A]
  {n:ℕ}
open Filter Work.G05 Finset
/-- All real multilinear jets through given order, not just derivative along some subset. -/
structure Response (n:ℕ)(f g:E→F)(x:E) : Prop where
   thatSide : ContDiffAt ℝ (n:ℕ∞) f x
   thisSide : ContDiffAt ℝ (n:ℕ∞) g x
   same (k:ℕ) (h:k≤n) : iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x

namespace Response
variable {f f' f'': E→ F}{x:E}
lemma here (h: Response n f f' x) : f x=f' x:=by have he:= congr($(h.same 0 (Nat.zero_le n)) 0); simpa using! he
lemma echo (h: Response n f f' x): Response n f' f x:=⟨h.thisSide,h.thatSide,fun _ hv=>(h.same _ hv).symm⟩
lemma trans (h₁: Response n f f' x)(h₂:Response n f' f'' x) : Response n f f'' x:=⟨h₁.thatSide,h₂.thisSide,fun i hi=>(h₁.same i hi).trans (h₂.same i hi)⟩
lemma refl (h:ContDiffAt ℝ (n:ℕ∞) f x): Response n f f x:= ⟨h,h,fun _ _=>rfl⟩
lemma stature (y:F)(x:E): Response n (fun _:E=>y) (fun _=>y) x:= refl contDiffAt_const
lemma eventual (h:ContDiffAt ℝ (n:ℕ∞) f x)(he:f =ᶠ[𝓝 x] f') : Response n f f' x:=⟨h, h.congr_of_eventuallyEq he.symm,fun k _=>(he.iteratedFDeriv ℝ k).eq_of_nhds⟩
lemma transit {v v':F→V}(h₁: Response n f f' x)(h₂: Response n v v' (f' x)):
    Response n (fun y=> v (f y)) (fun y=>v' (f' y)) x:=by
      have ht:ContDiffAt ℝ (n:ℕ∞) v (f x):= h₁.here.symm ▸ h₂.thatSide; exact ⟨ht.comp x h₁.thatSide,h₂.thisSide.comp _ h₁.thisSide,jets_comp h₁.thatSide h₁.thisSide ht h₂.thisSide h₁.here h₁.same h₂.same⟩
lemma vehicle {v:F→V} (h₁: Response n f f' x) (h₂ : ContDiff ℝ n v): Response n (fun i=>v (f i)) (fun i=>v (f' i)) x:=h₁.transit (refl h₂.contDiffAt)
lemma linear (h:Response n f f' x)(g:F→L[ℝ] V) : Response n (fun i=>g (f i)) (fun i=>g (f' i)) x:=h.vehicle g.contDiff
lemma plus {u u':E→F}(h₁: Response n f f' x)(h₂: Response n u u' x): Response n (fun i=>f i+u i) (fun i=>f' i+u' i) x:=by
   refine ⟨h₁.thatSide.add h₂.thatSide,h₁.thisSide.add h₂.thisSide, fun k hk=>?_⟩; change iteratedFDeriv ℝ k (f+u) x=iteratedFDeriv ℝ k (f'+u') x; have hd:(k:WithTop ℕ∞)≤(n:WithTop ℕ∞):= Nat.cast_le.mpr hk; rw [iteratedFDeriv_add_apply (h₁.thatSide.of_le hd) (h₂.thatSide.of_le hd),iteratedFDeriv_add_apply (h₁.thisSide.of_le hd) (h₂.thisSide.of_le hd), h₁.same k hk,h₂.same k hk] -- lemma names
lemma combo (Q : ℝ)(h:Response n f f' x) : Response n (fun i=> Q • f i) (fun i=>Q • f' i) x:=h.vehicle (by fun_prop)
lemma series {ι: Type*} (u:Finset ι)(f f':ι→E→F)(x:E)(h:∀ i∈u, Response n (f i) (f' i) x) : Response n (fun y=> ∑ i∈u, f i y) (fun y=>∑ i∈u, f' i y) x:=by
   induction u using Finset.induction_on with
   | empty=> simpa only [Finset.sum_empty] using stature (n:=n) (0:F) x
   | @insert a u ha ih=> simp_rw [Finset.sum_insert ha]; exact (h a (mem_insert_self ..)).plus (ih fun i hx=> h i (mem_insert_of_mem hx)) -- arg order
lemma both {g g':E→ E'}(h:Response n f f' x)(he:Response n g g' x) : Response n (fun i=> (f i,g i)) (fun i=>(f' i,g' i)) x:=by
   let p:=ContinuousLinearMap.inl ℝ F E'; let q:= ContinuousLinearMap.inr ℝ F E'; have hf(w:F)(z:E'):p w+ q z=(w,z):=by simp [p,q]; -- check
   simp_rw [← hf]; exact (h.linear p).plus (he.linear q)
lemma product {p q r t:E→A}(h:Response n p q x)(he: Response n r t x): Response n (fun i=>p i * r i) (fun i=>q i * t i) x:= (h.both he).vehicle (v:=fun w:A×A=>w.1*w.2) (contDiff_fst.mul contDiff_snd)
lemma smuls {q q':E→ℂ}{F : Type*} [NormedAddCommGroup F][NormedSpace ℝ F][NormedSpace ℂ F][IsScalarTower ℝ ℂ F]{f f':E→F}(h:Response n q q' x)(he:Response n f f' x): Response n (fun i=> q i • f i) (fun i=>q' i • f' i) x:= (h.both he).vehicle (v:=fun w:ℂ×F=> w.1 • w.2) (by fun_prop)
lemma blocked (h:ContDiffAt ℝ (n:ℕ∞) f 0): Response n (blockTaylor n f) f 0:= ⟨(blockTaylor_contDiff n f _).contDiffAt,h,blockTaylor_jets h⟩
lemma smooth_compare {f f':ℝ→UV.SpinPol n}(h:Response n f f' 0) : SourceRead.Agrees f f':=⟨h.thatSide,h.thisSide,fun i hi=> congr_arg (fun y:Tensor.T ℝ (UV.SpinPol n) i=> y (fun _=>1)) (h.same i hi)⟩
-- Fréchet→ordinary jets via cook.EFA.Store.
end Response
end YM.Massive.Papyrus
#print axioms YM.Massive.Papyrus.Response.smooth_compare
