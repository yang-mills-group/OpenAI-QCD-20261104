import YM.QCD.Eyrie.Moral

/-! # localization from holomorphic support of native path -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Rudder
open Revolve Work.F02 Metric Quarry Push.Uniform Stationary
open scoped Topology Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {I : Type} {k m : ℕ}
abbrev Road (n:Side):= Stationary.Lines su n 1
abbrev Cmp (n:Side):= Positions (Road n)
abbrev Sails (n:Side):= Laurent.Phase (Road n)
lemma orient (k:ℕ) {u:ℝ}(h:0<u): ∃ R C:ℝ,0<R ∧ 0≤C ∧∀ n (B:Bloom k) (i j:Row n),
    ∃ L:Sails n→ℂ, ContDiff ℂ ω L ∧ (∀ z:Sails n,z∈ball 0 R→ ‖L z‖≤ C* B.paid u)∧
       (∀ x:Cnr n,L (axisCL (Road n) x)=B.tonic 0 (input su n x) i j) :=by
  obtain ⟨r,hr,H⟩:= brush_bounds su h
  obtain ⟨C,hp,hC⟩:= paid_solo k h
  refine ⟨r,C,hr,hp,fun n B i j => ⟨(aval B i j) ∘ brush,(sticker_out B i j).comp brush_smooth,fun z hz=> hC n B i j 1 (brush z) (H n z (mem_ball_zero_iff.mp hz)), fun x=>?_⟩⟩
  change aval B i j (brush (_))=_; rw [show axisCL _ _=axes x from rfl, brush_physical, signed_sticker]

abbrev trailF (B: Bloom k)(i j: Row n): Cnr n→ ℂ := fun x=> (B.tonic 0 (input su n x)) i j

lemma walked (w : Walk) (x : Site n) (z : Site n) (h : z∈visits x w): separation x z≤ w.length:= by
  induction w generalizing x with
  | nil=> simp [visits] at h; rw [h]; simp
  | cons a w ih=>
    obtain hv|hv:= List.mem_cons.mp h
    · rw [hv]; simp
    have hp:=ih (x+a.vec) hv; have he:=separation_triangle x (x+a.vec) z; have hz : separation x (x+a.vec) ≤1:=letter_step x a
    rw [List.length_cons]; omega
lemma stopped (w : Walk) (x : Site n): separation x (stop x w) ≤ w.length:=walked _ _ _ (by induction w generalizing x with
  | nil=> simp [visits,stop]
  | cons a w ih => exact List.mem_cons_of_mem _ (ih _))
lemma touched (a:RG.Slot): (slotWalk a).length≤2*a.length:=by
  simp only [slotWalk,List.length_append,Lattice.reverse,List.length_map,List.length_reverse]; change _+4+_≤2*(a.walk.length+4); omega -- inspect
abbrev traceG (n:Side) (x:Road n):Site n:=x.1
lemma zone_g (i : Road n)(p : Cnr n)(q:ℝ)(z : Edge (Site n)) (hz : z.1≠traceG n i): input su n (p+q • Push.Uniform.bolt i) z=input su n p z := by
  rw [encode_link,encode_link]; congr 1; ext j
  have hp:i ≠ (z.1,Exterior.coord z.2,j):= fun e=> hz (congr_arg Prod.fst e).symm
  simp [arm_apply, Push.Uniform.bolt, Pi.single_apply,hp]
lemma abort (B:Bloom k) (i j:Row n) (a: Road n)(h : separation i.1 (traceG n a)>2* B.span) (x : Cnr n)(p:ℝ): trailF B i j (x+p • Push.Uniform.bolt a)=trailF B i j x:=by
  have he (w:Walk)(he:w.length≤2*B.span): travel (input su n (x+p • Push.Uniform.bolt a)) i.1 w= travel (input su n x) i.1 w:=travel_local i.1 w _ _ fun e hv _=> zone_g a _ p e (fun H=> by rw [← H] at h; have hh:=walked w _ _ hv; omega)
  have hv j : (B.petals j).atSite (input su n (x+p • Push.Uniform.bolt a)) i.1=(B.petals j).atSite (input su n x) i.1:= by
    simp_rw [atSite_curvature]; rw [he]
    apply (touched _).trans; unfold Bloom.span; gcongr; exact (single_le_sum (fun j (_:j∈univ)=>Nat.zero_le ((B.petals j).length)) (mem_univ _)).trans (Nat.le_add_left ..)
  unfold trailF; simp_rw [at_books,entryR, winding,Bloom.taste,hv]; rw [he B.tail (by unfold Bloom.span; omega)]
end YM.QCD.Eyrie
