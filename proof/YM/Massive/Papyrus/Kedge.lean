import YM.Massive.Papyrus.Homeward
/-! # Equivariant root sampling maps, on all spaces with given Radial resolution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus
open Lattice Wilson RG Source Function QCD Source.Drops UV Filter Work.G05 Finset Matrix Labels
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
open Scan Paper Boat
variable {H:Hol su}{d h:ℕ}
structure Kedge (H:Hol su)(d h:ℕ) where
   T (x:Cover)(U:Land): Mat
   tight (x) : Canvas (T x)
   home (U) : T 0 U=1
   gauge (k:Cover→su.El)(x U): T x (gaugeF k U)=Lat.colour (k 0)*T x U*star (Lat.colour (k x))
   pin (x:Cover)(s:Signed)(U): T x (scene s U)= T (s.act x) U
   charge (x U): T x (night U)=Mstar (T x U)
   germ (x) : Response d (fun i=> T x (trunkJ h H i)) (fun _=>1) 0
namespace Boat
variable (u:Flag H d h)(x:Cover)(s:Signed)(k:Cover→su.El)
local notation "M" => Mat
def mooring : Land→M:= if x=0 then fun _=> 1 else cabinA u x
lemma berth : Canvas (mooring u x):=by unfold mooring; split; exact counting _; exact cabinA_tight u _
lemma residence : mooring u 0=fun _=> 1:=if_pos rfl
lemma moor_gauge(U:Land) : mooring u x (gaugeF k U)=reshape (k 0) (k x) (mooring u x U):=by
   unfold mooring; split; next ht=> subst x; rw [reshape_apply,Matrix.mul_one,colourstar]
   exact cabinA_gauge ..
lemma moor_R (U:Land) : mooring u x (night U)=Mconj (mooring u x U):=by
   unfold mooring; split; · simp only [Mconj_apply,mstar_sq, star_one, Matrix.transpose_one]
   exact cabinA_R u x U
lemma moor_germ : Response d (fun x'=>mooring u x (trunkJ h H x')) (fun _=>1) 0:= by
  unfold mooring; split; · exact Response.stature (1:M) _
  exact cabinA_π u x

def hatch(s:Signed)(U:Land): M:= mooring u (s⁻¹.act x) (scene s U)
lemma hatch_gauge (U:Land): hatch u x s (gaugeF k U)= reshape (k 0) (k x) (hatch u x s U):=by unfold hatch; rw [scene_gauge,moor_gauge]; simp only [Signed.act_zero,Signed.act_inv]
lemma hatch_odd (U:Land): hatch u x s (night U)= Mconj (hatch u x s U):=by unfold hatch; rw [← night_scene,moor_R]
lemma hatch_lens : Response d (fun y=>hatch u x s (trunkJ h H y)) (fun _=>1) 0:=by
   unfold hatch; simp_rw [← landscape]; let L:= rot s.ortho⁻¹ h; have hv: L 0=0:=map_zero _; exact (Response.refl L.contDiff.contDiffAt).transit (v':=fun _=>1) (hv.symm ▸ moor_germ u _)
private lemma hatch_note (f:Signed→M)(A: M→L[ℝ]M): MeanF (fun i=>A (f i))= A (MeanF f):=by unfold MeanF; rw [map_smul,map_sum]
def lodge (x:Cover)(U:Land): M:= MeanF (fun i=>hatch u x i U)
lemma hatch_home(U:Land): lodge u 0 U=1:=by unfold lodge hatch; simp_rw [Signed.act_zero, residence]; exact tone (1:M)
lemma hatch_actual(U:Land) : lodge u x (gaugeF k U)= Lat.colour (k 0)* lodge u x U * star (Lat.colour (k x)):=by unfold lodge; simp_rw [hatch_gauge]; rw [hatch_note,reshape_apply]
lemma hatch_real(U:Land): lodge u x (night U)=Mstar (lodge u x U):=by unfold lodge; simp_rw [hatch_odd]; rw [hatch_note,Mconj_apply]
lemma hatch_city(U:Land): lodge u x (scene s U)=lodge u (s.act x) U:=by
   unfold lodge; symm; rw [← mean_r _ s]; unfold hatch; simp_rw [scene_slide,_root_.mul_inv_rev, Signed.act_mul, Signed.inv_act]
def roller (H:Hol su)(d h:ℕ)(u:Flag H d h) : Kedge H d h where
   T:=lodge u
   tight x:= (Canvas.annual _ _ (fun i _=> (berth u (i⁻¹.act x)).sees i)).scale _
   home:=hatch_home u
   gauge k x:=hatch_actual u x k
   pin:=hatch_city u
   charge:=hatch_real u
   germ x:= accumulated d _ _ (hatch_lens u x)
end Boat
end YM.Massive.Papyrus
#print axioms YM.Massive.Papyrus.Boat.roller
