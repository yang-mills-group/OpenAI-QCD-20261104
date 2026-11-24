import YM.Eden.Priam
/-! # commissions at actual parity.Sequence boot one named marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Inky
open QCD QCD.Lat Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory
open Precision Exterior Bloch Laurent
open QCD.Creek QCD.Cove QCD.Flume QCD.Free YM.Next.Free
open YM.Arise YM.Arise.Count YM.Bloom YM.Bloom.TreeP YM.Bloom.Jar
open Ribbon Cape Play Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit
open Rebus Matrix Vest TimesV Arise.Bill Arise.Range Grass QCD.Eden YM.Eden
open QCD.Bloom QCD.Bloom.Buzz YM.Next.Rank.Normal Massive.UV Arise.Parcel
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
variable {c f:Side}{A J K X Y I:Type}[Fintype A][Fintype J][Fintype K][Fintype X][Fintype Y][Fintype I]
variable {k d i j m n B L D:ℕ}{a b ε s C C' v:ℝ}
variable (W:ℝ)(x:I→ Cover)(p:I→ℕ)(q:I→Bool)(i:I)
variable (H: Bed)(F: Train j) (ht:(chalkW f H).IsSymm) (hQ:(YM.Eden.milky 0 H f (G:=su) (d':=p i)).IsSymm)
local notation "Tπ" => shone p x W f H F ht
local notation "Yp"=> beamG p x W f
local notation "Yq"=> beamL p x W f
local notation "Z"=> Tv p
local notation "Wi"=>p i
local notation "Si"=> q i
local notation "x₀"=>x i
local notation "Sν"=> Spine I
local notation "R"=>rider
local notation "P"=> shape (linkS p i)
local notation "Qb"=>oxide Sigma.fst (Yq*Buzz.start f F 6*Matrix.transpose Yq)
local notation "Ω"=>Buzz.start f F 6
local notation "E"=>gateP Wi W
local notation "Vg"=>mood Wi x₀ (1:Grid f)
include ht -- maybe
variable (hj:2≤ j)
include hj
lemma originS : P * Qb * (P).transpose = E * corsage F f Wi 0 * (E).transpose:=by
    ext v w; rw [leg_v]; rw [oxide,of_apply,if_pos (show _=_ from rfl)]; rw[← evolS x₀ F hj, corsage];  rw [Matrix.mul_neg,Matrix.neg_mul,Matrix.neg_apply]; let X:= Yq*Ω*(Yq).transpose; change -(X _ _) = _; rw [← leg_v (linkS p i) X]; unfold X; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.mul_assoc _ ((Yq).transpose),← Matrix.transpose_mul,lottS]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
local notation "κP"=> Ribbon.stake (Keys f 6) (Ribbon.burst q (Singleton.singleton i))
lemma sharedS (v:Grace Wi Si): (splash (Tπ).M (Tπ).V (house q p i v)).val = κP (rateS Wi x₀ (1:Grid f) (rosewood F f Wi (changeVars E v.val))) :=by
     rw [show (Tπ).M= _ from (show (Tπ).M= breezeP Sν Yq from rfl),show (Tπ).V= _ from (show (Tπ).V=breezeX Sν Qb from rfl),rimy,show (house q p i v).val = Ribbon.stake (Arms p) _ (ham I i p v.val) from rfl,speaks]; unfold rateS rosewood; let V:=v.val; have htA:ham I i p V=changeVars P V:=(keeper _ _).symm
     apply congr_arg; change changeVars (Yq) (Creek.birth (Wand Qb) (ham _ _ _ V))=changeVars Vg (Creek.birth (Wand (corsage F f Wi 0)) (changeVars E V))
     rw [htA,Anomaly.transfer,Anomaly.transfer,Massive.UV.multipleChange, Massive.UV.multipleChange, originS W x p i H F ht hj,lottS]
omit ht hj
noncomputable def fareC (d:ℕ)(p: Bool): Cups d p→ₗ[ℂ] Bard d:= TensorProduct.map LinearMap.id (Grace d p).subtype
variable {r:Clip}(ht':Floor H r f a b)(ha:0<a)
local notation "Xw"=> Kh f
local notation "Zq"=>Dh f 6 I
include ht ht' hj hQ ha
lemma rexT (q': Cups Wi Si)(U: Grid f)(σ:ℝ) : (Oce.rose Zq (karm σ U) ((Tπ).read (port q p i q'))).val= κP (taxP Wi x₀ U σ⁻¹ (reelW Wi H f F hQ (padU Wi W (fareC Wi Si q')))):=by
     induction q' using TensorProduct.induction_on with
     | zero=> simp only [map_zero]; rfl
     | add p q h hp=> simp only [map_add,Subalgebra.coe_add,h,hp]; -- need type class Patio
     | tmul l r=> rw [portal,Tone.spree,Oce.antiquity];
                  change (Oce.eve (karm σ U) _ :ℂ) • (splash _ _ _).val=_; rw [show (Tπ).P=Yp from rfl, gloria W x p i H F ht hQ ht' ha]; let Vz:= Next.Rank.Normal.milk (wager _ _ _ hQ) (stemsP su Wi W l); have he : taxG Wi x₀ U σ⁻¹ Vz = Oce.eve (karm σ U) (exchange (spool (chartD x₀ Wi)) Vz):= lender ..; rw [← he];
                  unfold fareC reelW padU; rw[TensorProduct.map_tmul, TensorProduct.map_tmul,TensorProduct.map_tmul,testimonP, sharedS W x p q i H F ht hj]; rw [map_smul]; rfl
end YM.MassiveQCD.Inky
#print axioms YM.MassiveQCD.Inky.rexT
