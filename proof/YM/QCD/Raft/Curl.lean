import YM.QCD.Raft.Line

/-! # fine gradient column at each alias. not demanded on off-mesh interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f n:Side}{I J K:Type}[Fintype I] [DecidableEq I]
def remedy (a : Axis)(v:Co n I→ℂ)(p:Co n I):ℂ:=v (p.1+ step a,p.2)-v p
lemma remediate {v:J→Co n I→ℂ}(s:Finset J)(a:Axis):remedy a (∑ i∈s,v i)=∑ i∈s, remedy a (v i):=by
  funext x; simp only [remedy,Finset.sum_apply,← sum_sub_distrib]
lemma fast (v:I→ℂ)(x:Site n){p:Momentum}(h: Matches p x)(i:Axis): remedy i (vw x v)=vw x ((q p i) • v):=by
  funext ⟨k,j⟩; unfold remedy vw; rw [cell_add,h.step]; simp only [q,Pi.smul_apply,smul_eq_mul]; ring
variable {L:Side}{T:Towers L}{H V:Bed}{η A U:ℝ}{k:ℕ}
def rayBudget (p:Momentum)(b: TypeFace 1→ℂ)(T:Towers L) (x:Site L):= profile T.A0 p x *ᵥ b
set_option maxHeartbeats 30000 in
lemma relay_pitch (hp:0<η)(hk:1 ≤ k)(ht:T.Deep η A k) (hH:H.dual_diag.strip η A)(hV: V.diagonal.strip η U)
    (h:f.val=c.val*L.val) (hi:H.diagonal.acts f * H.dual_diag.acts f = 1) (ho:Odd L.val)
    (hh : installed (Ratio.mk L h) T.T * V.diagonal.acts c * Exterior.d 1 c = H.diagonal.acts f * d 1 f * installed ⟨L,h⟩ T.A0)
    {a: Axis} (z:Cover) (x:Site L)(b:TypeFace 1→ℂ):
    let R:= quant c z; let p:= aliasAt R x
    q p a • (symbol 1 p *ᵥ rayBudget R b T x) = profile (psi H V T (some a)) R x *ᵥ (symbol 1 R *ᵥ b) :=by
  intro R p
  let g:Ratio c f:=⟨L,h⟩; let F:= symbol 1 R*ᵥ b
  let w:= wrap c z; let C:= vw w b
  let M (a:Option Axis):= installed g (psi H V T a)
  let X:= fun i:Site L=> aliasSite g z i
  have hB : Row.safe T.A0:=Row.rights _ _ ((ht.2.2.2 [] (Nat.zero_le _)).1) hp.le -- inspect
  have hz: cmat (M none)*ᵥ (vw w F)= cmat (d 1 f)*ᵥ (cmat (installed g T.A0) *ᵥ C):=by
    have hE: vw w F= cmat (Exterior.d 1 c)*ᵥ C:=(gradient_s (p:=w) (quant_matches c z) b).symm
    have hm: M none * Exterior.d 1 c=Exterior.d 1 f*installed g T.A0:=psi_curl hp hH hV hk ht h hi hh
    calc
      _ = cmat (M none * Exterior.d 1 c) *ᵥ C:=by rw [cmat_mul, hE,Matrix.mulVec_mulVec]
      _ = cmat (Exterior.d 1 f*installed g T.A0) *ᵥ C:=by rw [hm]
      _ = _:=by rw [cmat_mul,Matrix.mulVec_mulVec]
  have he i :Matches (aliasAt R i) (X i):=alias_match g z i
  have hP (U: Co c (TypeFace 2)→ℂ): remedy a (cmat (M none)*ᵥ U)=cmat (M (some a))*ᵥ U:=by
    funext i; apply Complex.ext
    · change vision _ i=vision _ i; rw [see, psi_read hp hH hV hk ht h ho]; unfold remedy vision; rw [Complex.sub_re]; change vision (cmat (M none)*ᵥ U) (i.1+step a,i.2)-vision (cmat (M none) *ᵥ U) i= _; rw [see]; rfl
    · change desire _ i=desire _ i; rw [believe,psi_read hp hH hV hk ht h ho]; unfold remedy desire; rw [Complex.sub_im]; change desire (cmat (M none)*ᵥ U) (i.1+step a,i.2)-desire (cmat (M none) *ᵥ U) i= _; rw [believe]; rfl
  apply congr_fun (gotcha (g:=g) z (fun i=> q (aliasAt R i) a • (symbol 1 (aliasAt R i) *ᵥ rayBudget R b T i)) (fun i=> profile (psi H V T (some a)) R i *ᵥ F) ?_) x
  have hR:= hP (vw w F); rw [hz, show cmat (installed g T.A0) *ᵥ C=_ from vw_raze g z T.A0 hB b,sendS] at hR
  change remedy a (∑ i:Site L, cmat (Exterior.d 1 f)*ᵥ vw (X i) (rayBudget R b T i))= _ at hR
  simp_rw [show ∀ i:Site L, cmat (Exterior.d 1 f)*ᵥ vw (X i) (rayBudget R b T i) = _ from fun i=> gradient_s (he i) _] at hR; rw [remediate] at hR; simp_rw [show ∀ (i:Site L) a y,remedy a (vw (X i) y (I:=TypeFace 2))=_ from fun i a y=> fast y (X i) (he i) a] at hR; exact hR.trans (vw_raze g z (psi H V T (some a)) (Row.rights _ _ (psi_strip hp hH hV hk ht (some a)) hp.le) F)
end YM.QCD.Raft
