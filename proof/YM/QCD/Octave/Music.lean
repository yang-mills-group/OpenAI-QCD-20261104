import YM.QCD.Oasis.Sea
import YM.QCD.Reggae.Scalar
import YM.QCD.King.Rings
/-!
# Instrument assembly. Sample exact slice potential no hard labels. Warm and cool trial. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
section step
open scoped Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}{S:StepData c f} (F:Forest S.ratio) {Z:ℝ}{j:ℕ}
local notation "X"=>Positions (Uniform.Primary c G) × Poll.Body (Precision.Key F G)
abbrev projection (x:X):= F.drape (draw F (represent (Uniform.tint G _ x.1)) x.2)
def fabric (G:Gauge)(j:ℕ)(Z:ℝ):= (1+fineCost G j Z)*1
lemma tempoP (h:PaintSupply G j Z)(x:X)(hx:‖x‖≤1): Mode (projection F) x j (fabric G j Z):=by
    let i:=fineCost G j Z; let W:= (combineH (G:=G) F).toContinuousLinearMap; have hp:=fine_supply F h; have hy :=((W.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (feesComb F))).trans hx
    have he:0 ≤ i:=hp.2.1
    refine ⟨mul_nonneg (by linarith only [he] : 0≤1+i) zero_le_one,fun i=>?_⟩; have hr:=hp.2.2 i _ hy; have hx := Brush.reading W (offer.2 ⟨hr.analytic.of_le le_top, hr.norm_le⟩) (feesComb F); rw [one_mul] at hx; exact thicken (f:=fun x=>projection F x i) hx
end step
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Matrix.Norms.L2Operator
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio){β a b t u v Z w p r:ℝ}{N j l k i d:ℕ}
variable {x:Positions (Uniform.Primary c su) × Poll.Body (Precision.Key F su)}
local notation "X"=>Positions (Uniform.Primary c su) × Poll.Body (Precision.Key F su)
lemma meter {D E:Type}[Fintype D][Fintype E][DecidableEq D][DecidableEq E]{p:D→Site f}{q:E→Site f}{T:Grid f→ArrayL D E}(h:Heritage p q t a l T b)(ht:0<t)(hb:0≤b)(ha:0≤a)(he:Mode (G:=su) (projection F) x j Z):Brush j (clump j ((massQ+massQ)*(1+Z)^j) (letterP t j*b)) 1 (T ∘ projection F) x :=by -- x type not Grid
   obtain ⟨U,V,h⟩:=h; let g:=Kit.settled∘ projection (G:=su) F; have hv {i}(hi:i∈ball (g x) t): i∈Kingdom f t:= Set.mem_iUnion.mpr ⟨_,hi⟩
   have hz:= composite (retro he|>.trim) (beau (x:=g x) ht (fun _ hi=>h.won _ (hv hi)) (fun _ hi=> h.empire ha hb _ (hv hi)) j)
   exact hz.shimmy (Eventually.of_forall fun i=> Eq.symm (h.winched ..))
open Revolve
variable {O:Flight j k}(e:f.val=c.val*O.L.val)(T:Grid f→ Sheet f)(W:ℕ → Atom su 2)
open Loom Fleet
lemma wearCost (U:Sheet c)(hx:0<a): ‖wearK c N a (paleF N U)‖ ≤ a^2*(Fintype.card (Lat.Modes c N))^2*‖U‖ :=by -- a positive
   change Creek.load _ (Grass.form (Lat.copies N U))≤ _; refine (fauna _ (by assumption)).trans ?_
   unfold jacket; have h i j:‖Lat.copies N U i j‖≤ ‖U‖:=by unfold Lat.copies; rw [Matrix.blockDiagonal_apply]; split; apply Cost.north; rw [norm_zero]; exact norm_nonneg _
   calc _ ≤ a^2 * ∑ _i: Lat.Modes c N,∑ _j:Lat.Modes c N, ‖U‖:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=> sum_le_sum (fun j _=>h i j)) (sq_nonneg _)
        _ = _ :=by simp; ring
lemma highGeom (N:ℕ):∃ R : ℝ,0≤R ∧ ∀ c:Side,(Fintype.card (Lat.Modes c N):ℝ)=R*Fintype.card (Site c):=by exact ⟨Fintype.card Lat.Fiber *N,by positivity,fun c=> by simp only [Lat.Modes, Modes,Row,Fintype.card_prod,Flavor,Fintype.card_fin]; push_cast; ring⟩
-- real-linear for C norm estimates.
def powerZ (c:Side)(N:ℕ)(a:ℝ): Sheet c→L[ℝ] EvenA c N:= LinearMap.toContinuousLinearMap (wearK c N a).toLinearMap|>.restrictScalars ℝ |>.comp ((Stew.nozzle c N).restrictScalars ℝ)
lemma billed (ha:0 < a) (c:Side)(N:ℕ) : ‖powerZ c N a‖ ≤ a^2*(Fintype.card (Lat.Modes c N))^2:= ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun i=> wearCost i ha
lemma colP (c: Side)(N:ℕ) : ‖baker c N‖ ≤ 1:=by
   apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; change ‖x • (1:EvenA c N)‖ ≤ _; rw [norm_smul,norm_one,mul_one]
def alti (f:Side): Sheet f→L[ℝ] ℝ := LinearMap.toContinuousLinearMap { toFun:=fun T=> ∑ i:Site f,(cell T i i).trace.re,map_smul':=fun i v=>by rw [RingHom.id_apply,show i • _= i* _ from rfl,mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [show cell (i • v) _ _=i • cell v j j from rfl,Matrix.trace_smul]; simp,map_add':=fun i j=>by simp only [show ∀ l, cell (i+j) l l= cell i l l + cell j l l from fun _=> rfl, Matrix.trace_add,Complex.add_re,sum_add_distrib] }
lemma ascent (f:Side): ‖alti f‖ ≤ (Fintype.card (Site f):ℝ) *Fintype.card Lat.Fiber:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro T; refine (norm_sum_le ..).trans ?_; apply le_trans (sum_le_sum (f:=fun i=>‖(cell T i i).trace.re‖) (g:=fun _=> Fintype.card Lat.Fiber*‖T‖) (fun i _=>?_)) (by simp only [Finset.sum_const,card_univ,nsmul_eq_mul]; rw [mul_assoc]); apply (Complex.abs_re_le_norm _).trans; unfold Matrix.trace; apply (norm_sum_le ..).trans; exact (sum_le_sum (g:=fun _=> ‖T‖) (fun j _=> Cost.north T (i,j) (i,j))).trans_eq (by simp)
end YM.QCD.Octave
