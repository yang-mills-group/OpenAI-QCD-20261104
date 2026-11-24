import YM.QCD.Agate.Slide
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D S:Lot}
open Tide Flume YM.Next.Free Kites
open Acre.Rails.IV Land.Wall
variable (W: Wall)(he: Even c.val) (hm:W.Within D S)
lemma shunts (s: Signed)(t:Cover)(k: Site c)(r:Site c) (h:∀ i:Cover, leap k (affine s t i)=affine s r (leap k i))(U:Grid c): expandAt k (pull s r U)=pull s t (expandAt k U):=by
      funext j; obtain ⟨x,i⟩:=j; let a:=(posDir i).rotate s
      change a.read U (affine s r (leap k x))=a.read (expandAt k U) (affine s t x); rw [← h]; unfold Lattice.Step.read Lattice.Step.used; split <;> (first | split | skip) <;> simp [expandAt,leap,map_sub,wrap_step,add_sub_right_comm]
lemma rideX (U:Grid c): lenses W.mirror W.save hm (crest (origin c) U)=crest (origin c) ((FaceR W he).pullC su U):=by
   simp_rw [atone]; rw [lenses_at]; apply congr_arg; symm; exact shunts _ _ _ _ (lifting W he) _
noncomputable def flash (x:Paper D F): Paper S F:=fun U=> W.flips hm (x (lenses W.mirror W.save hm U))
lemma scenic (x: Poly D F): pass (pens (origin c)) (W.flips hm x) = theta (FaceR W he) (pass (pens (origin c)) x):=by
  let T:=FaceR W he; let q:=origin c
  let U := (pass (pens (D:=S) (F:=F) q)).toLinearMap.comp (W.flips hm)
  let V := (theta T).comp (pass (pens (D:=D) (F:=F) q)).toLinearMap
  apply LinearMap.congr_fun (f := U) (g := V)
  apply ext_reversing (by intro x y; simp only [U,flips,LinearMap.comp_apply,tilt_mul,AlgHom.toLinearMap_apply,map_mul])
    (by intro x y; simp only [V,LinearMap.comp_apply, AlgHom.toLinearMap_apply,map_mul,theta_mul]) (by simp [U,V,flips,theta])
  rintro (⟨⟨u,j⟩,k⟩|⟨⟨u,j⟩,k⟩)
  · change pass _ (pass _ (tilt (copies _ _) (psi (place u (j,k)))))=theta _ (pass _ (psi (place u (j,k))))
    rw [tilting_psi (Equiv.refl (Court D)) rfl,pass_psi (pens _) (place u (j,k)),show pens q (place u (j,k))=place (leap q u.val) (j,k) from rfl,theta_psi]
    simp only [map_sum,map_smul,pass_bar]; rw [show T.reflect (leap q u.val)= _ from (lifting W he u.val).symm]; rfl
  change pass _ (pass _ (tilt (copies _ _) (bar (place u (j,k)))))=theta _ (pass _ (bar (place u (j,k))))
  rw [tilting_bar (Equiv.refl (Court D)),pass_bar (pens _) (place u (j,k)), show pens q (place u (j,k))=place (leap q u.val) (j,k) from rfl,theta_bar]
  simp only [map_sum,map_smul,pass_psi]; rw [show T.reflect (leap q u.val)= _ from (lifting W he u.val).symm]; rfl
lemma scenery (x:Paper D F): jewel (origin c) (flash W hm x)=foldsT (FaceR W he) (jewel (origin c) x):=by
    funext U; unfold jewel flash; rw [scenic,rideX]; rfl
-- sign equality
include hm
lemma twin (x:Poly D F)(h:∀ i:Court D,(Tide.simple (FaceR W he)).stamp (leap (origin c) i.val)=chrom W)(hh:∀ i:Court S,(Tide.simple (FaceR W he)).stamp (leap (origin c) i.val)=chrom W):
    let P:=Tide.simple (FaceR W he); P.tape F (theta (FaceR W he) (P.tape F (pass (pens (origin c)) x)))=theta (FaceR W he) (pass (pens (origin c)) x):=by
    intro P; let Y:= FaceR W he; let M:= origin c
    by_cases H:W.post<0
    · -- tape interwin grade. simplify tilt_comm
      have hg(A:Lot)(hp:∀ i:Court A,P.stamp (leap M i.val)=chrom W)(x:Poly A F): P.tape F (pass (pens M) x)=pass (pens M) (grade x):=by
          refine AlgHom.congr_fun (φ₁:=(P.tape F).comp (Grass.pass (pens (D:=A) (F:=F) M))) (φ₂:=(Grass.pass (pens (D:=A) (F:=F) M)).comp Grass.grade) ?_ x
          apply ext_atoms; rintro (i|i)
          · change P.tape F (pass _ (psi i))=pass _ (grade (psi i)); rw [pass_psi,P.tape_psi,show P.stamp (pens M i).1.1=_ from hp i.1.1]; simp [chrom,H,show Grass.grade (psi i)=-psi i from grade_atom _]
          change P.tape F (pass _ (bar i))=pass _ (grade (bar i)); rw [pass_bar,P.tape_bar,show P.stamp (pens M i).1.1=_ from hp i.1.1]; simp [chrom,H,show Grass.grade (bar i)=-bar i from grade_atom _]
      change P.tape F (theta Y (P.tape F (pass (pens M) x)))= _; rw [hg D h]
      have ht: theta Y (pass (pens M) (grade x))=grade (theta Y (pass (pens M) x)):=by rw [← pass_grade,theta_grade] -- check
      rw [ht,← scenic W he hm,pass_grade, hg S hh]; simp [M]
    have hg(A:Lot)(hp:∀ i:Court A,P.stamp (leap M i.val)=chrom W)(x:Poly A F): P.tape F (pass (pens M) x)=pass (pens M) x:=by
         refine AlgHom.congr_fun (φ₁:=(P.tape F).comp (pass _)) (φ₂:=pass _) (ext_atoms ?_) x; rintro (i|i)
         · change P.tape F (pass _ (psi i))=pass _ (psi i); rw [pass_psi,P.tape_psi,show P.stamp (pens M i).1.1=_ from hp i.1.1]; simp [chrom,H]
         change P.tape F (pass _ (bar i))=pass _ (bar i); rw [pass_bar,P.tape_bar,show P.stamp (pens M i).1.1=_ from hp i.1.1]; simp [chrom,H]
    rw [hg D h,← scenic W he hm]; exact hg S hh _
end YM.QCD.Agate
