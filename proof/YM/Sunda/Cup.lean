import YM.Sunda.Ocean
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
open Massive.Oriole Compass MassFields Signals
lemma transposeK(s:Signed)(i:Axis): Averaging.permute s (atVector i) = atVector (s.perm i):=by
     unfold Averaging.permute atVector; refine congr_arg some ?_; funext l; obtain ⟨u,rfl⟩:= s.perm.surjective l; simp
lemma isot(s:Signed):Averaging.permute s isotropic=isotropic:=rfl
include J H JQ B R S
variable (y:Bool)(a b:Flavor 6)
local notation "V"=> axisP a b y K
local notation "J'"=> lever a b y K
lemma owe : properScalar (X0) (J'):=by
     refine legitimate J H JQ B R S y J' (fun p s hs=>?_) ?_
     · rw [S.acts JQ.h (loans J H JQ B R) _ _ hs]; unfold lever; rw[T.w _ s hs,isot,← map_smul]; refine congr_arg _ (Subtype.ext ?_); rw[P.sym.pinActs]; change pinAct p (bilinear a b (pulp y) _ _)= _; rw [acclaim a b s p hs,marked_root,one_mul,Complex.ofReal_one,one_smul,hem_ground,pulpP,Oriole.nourish]; rfl
     exact JQ.h.tops _ _ ▸ LinearMap.mem_range_self ..
lemma owns : properVector (X0) V:=by
     refine earnsV J H JQ B R S y V (fun p s hs i=>?_) (fun i=>?_)
     · rw [S.acts JQ.h (loans J H JQ B R) _ _ hs, feeSign y V p s hs]; unfold axisP; rw[T.w _ s hs,transposeK, ← map_smul]; refine congr_arg _ (Subtype.ext ?_); rw [P.sym.pinActs]; change pinAct p (bilinear a b (claw y i) _ _)= _; rw [acclaim a b s p hs,marked_root,one_mul,Complex.ofReal_one, one_smul,hem_ground,foxW y p s hs,Oriole.nourish]; rfl
     refine JQ.h.slope (show 6 ≤ 8 from by decide) ?_; unfold axisP; rw [← JQ.h.tops (atVector i)]; exact LinearMap.mem_range_self ..
lemma ownsT (z: Signals)(h:z.Masses)(hx:Arbit z K): z.PCAC (X0) MassM:= destiny T z ρ A.jet hx h (fun i j y _=> owns J H JQ B R S y i j) (fun i j y _=> owe J H JQ B R S y i j)
end YM.Mako
#print axioms YM.Mako.ownsT
