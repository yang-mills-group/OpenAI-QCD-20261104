import YM.QCD.Tide.Lumen
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Revolve
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C] {n c f : Side} {F : ℕ} {β:ℝ} {R:Cells.Cut c} {r:Ratio c f}
open Flume YM.Next.Free
noncomputable def lens (R:Cells.Cut c):=hues R.slide R.flip (inc R) (gamma R.pos)
lemma lensP (R:Cells.Cut c): let k:= simple R; let A:= rides (RP.perm R) (fun _=> RP.lamp R.pos); lens R=k.tag*A*k.tag:=by
    intro k A; unfold lens hues; unfold A; rw [Tape.tags,ride_mul,ride_mul, Equiv.refl_trans,Equiv.trans_refl]; congr 1
    · ext1; rfl
    funext i; simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,gamma_star]; rw [mul_comm]; rfl
lemma lens_star (R:Cells.Cut c): star (lens R)=lens R:=by
    let k:=simple R; let A:=rides (RP.perm R) (fun _=> RP.lamp R.pos); rw [show lens R=_ from lensP R,star_mul,star_mul]; change _=k.tag*A*k.tag; rw [k.tag_star,show star A=A from ?_]; rw [mul_assoc]
    unfold A; simp [ride_ad]
lemma lens_sq (R:Cells.Cut c): lens R * lens R=1:=by
    let k:=simple R; let A:=rides (RP.perm R) (fun _=> RP.lamp R.pos); rw [show lens R=k.tag*A*k.tag from lensP R]; simp only [mul_assoc]; rw [← mul_assoc k.tag k.tag,k.tag_sq,one_mul,← mul_assoc A, show A*A=1 from ?_,one_mul,k.tag_sq]
    unfold A; rw [ride_mul,show (RP.perm R).trans (RP.perm R)=Equiv.refl _ from Equiv.ext fun i=>R.twice i]; simp only [lamp_sq]; exact ridden
lemma tracks (R:Cells.Cut c)(F:ℕ): let k:=simple R; copies F (lens R)= (k.bands F)*RP.folds R F*k.bands F:=by
    intro k; rw [show lens R=_ from lensP R,k.band_copies,copies_mul,copies_mul]; rfl
lemma crownsH (T U:Matrix A A ℂ)(h:T.transpose=T)(he: Twist T=T) (x:Dirac A): tilt (T*U*T) x=adapter T T (tilt U (adapter T T x)):=by
    rw [tilts, tilts,turns,adapt_together,adapt_together]; simp only [he,Matrix.transpose_neg,Matrix.transpose_mul, h,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]
lemma lensF (R:Cells.Cut c)(x:Fields c F): tilt (copies F (lens R)) x=(simple R).tape _ (theta R ((simple R).tape _ x)):=by
    let k:=simple R; let Z:= k.bands F; let U:=RP.folds R F; have he: Twist Z=Z:=by unfold Twist; rw [← Matrix.star_eq_conjTranspose,show star Z=Z from k.band_star _]; exact k.band_trans _
    rw [show copies _ _=Z*U*Z from tracks ..]; exact crownsH Z U (k.band_trans _) he x
lemma curved (h:R.kind=.link) (x:Cover)(U:Grid c)(o:Lattice.Order):
 routeM 0 (pull R.flip R.slide U) (route 0 x o)*lens R=lens R*routeM 0 U (route 0 (R.flip.act x) (orderEquiv R.flip o)):=by
    have hp(w:Walk): routeM 0 (pull R.flip R.slide U) w*lens R=lens R* routeM 0 U (w.map (·.rotate R.flip)):=by
        induction w with
        | nil=> simp [routeM]
        | cons a w ih=> change leg 0 _ a *routeM 0 _ w*lens R= _; rw [mul_assoc,ih, ← mul_assoc, show leg _ _ _*lens R= _ from turned_leg (glances R h) (gamma _) U a,mul_assoc]; rfl
    rw [hp,send_route _ _ _ _ 0]; simp [aura,affine]
variable {i j:ℕ} (P:Flight i j)(hf:f.val=c.val*P.L.val)
lemma towers (h:R.kind=.link): let r:=sliceL P hf; let T:= gateH R r; ∀ U : Grid f,tied P hf 0 (T.pullC su U)=lens R*tied P hf 0 U*lens T:=by
    intro r T U; let X:= lens R; let Y:= lens T; let V:= T.pullC su U; let s:=R.flip;
    have hs : scoop r*lens T=lens R*scoop r:=by
         have hi:lens T=hues (r.embed R.slide) R.flip (inc T) (gamma R.pos):=by rw [slippery R r h P.odd]; rfl
         rw [hi, dream,show inc T∘r.embed=inc R from funext (income R r h P.odd)]; rfl
    have he (o:Lattice.Order): lineF P hf 0 V o*Y=X*lineF P hf 0 U (orderEquiv s o):=by
         unfold lineF; rw [Matrix.sum_mul,Matrix.mul_sum, ← Equiv.sum_comp (starry P.patch s) (fun i=> X*((P.patch.weight i:ℂ) • (scoop r*routeM 0 U (route 0 i.val (orderEquiv s o)))))]; refine sum_congr rfl fun i _=>?_
         rw [alternate, Matrix.mul_smul,Matrix.smul_mul]; congr 1; change scoop r*routeM 0 _ _*lens T=_; rw [Matrix.mul_assoc,show routeM 0 (T.pullC su U) _ * lens T= _ from curved (R:=T) rfl i.val U o,← Matrix.mul_assoc, hs,Matrix.mul_assoc]; rfl
    have hp: tied P hf 0 V * Y= lens R *tied P hf 0 U:=by
         unfold tied; simp only [Matrix.smul_mul,Matrix.mul_smul, Matrix.sum_mul, he,Matrix.mul_sum]; congr 2
    change tied _ _ _ V=lens R*_ * Y; rw [← hp, Matrix.mul_assoc,show Y*Y=1 from lens_sq T,Matrix.mul_one]
end YM.QCD.Tide
