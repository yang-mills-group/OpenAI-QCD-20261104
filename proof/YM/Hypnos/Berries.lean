import YM.Hypnos.Vela
import YM.Hypnos.Spokes
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TellerFold
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}
open Current
-- work on full color native lift
namespace Fruit
abbrev Col (G:Gauge) (n:Side):= FreeResolvent.Slot G n 2
def coeff (G:Gauge)(n:Side)(H:Bed) := FreeResolvent.tensor G (learned H n)
def view (G:Gauge)(S:StepData c f)(H H': Bed)(T : Towers S.patch.L) := FreeResolvent.tensor G (psi S H H' T)
def curtain (G:Gauge)(S:StepData c f)(H H':Bed)(T:Towers S.patch.L): Matrix (Col G f) (Col G f) ℝ:= FreeResolvent.tensor G (fConditional S H H' T)
lemma inverse_f (G:Gauge) (S:StepData c f)(H H':Bed)(T:Towers S.patch.L):
    coeff G f H=curtain G S H H' T +view G S H H' T*coeff G c H'*(view G S H H' T).transpose:=by
    unfold coeff view curtain fConditional; rw [tensor_sub,tensor_mul,tensor_mul,FreeResolvent.tensor_transpose,sub_add_cancel]
lemma chargedC {η C:ℝ}{p:Clip}(G:Gauge)(H:Bed)(n:Side)(h: Floor H p n η C)(he:0<η): (coeff G n H).IsSymm:=by
    unfold Matrix.IsSymm coeff; rw [FreeResolvent.tensor_transpose, show (learned H n).transpose=learned H n from flux_symm _ _ ⟨fun v=> (h.uniform.1 v).1⟩ he h.symmetric.1]
lemma heals (G:Gauge)(S:StepData c f)(H H':Bed)(T:Towers S.patch.L)(h:(coeff G f H).IsSymm)(he:(coeff G c H').IsSymm): (curtain G S H H' T).IsSymm:=by
    rw [show curtain G S H H' T=coeff G f H-view G S H H' T*coeff G c H'*(view G S H H' T).transpose from by rw [inverse_f]; abel]
    unfold Matrix.IsSymm; simp only [Matrix.transpose_sub,h.eq,Matrix.transpose_mul,he.eq,transpose_transpose,Matrix.mul_assoc]

-- actual prices.Bridge comparison with air X
variable (X:Coat T F)(H H':Bed)(T₀ : Towers S.patch.L) (u:Directions G c) (w:Air f G)

def jet {n: Side} (p:Directions G n) : Col G n→ℝ := FreeResolvent.flatten (Exterior.dColor G n 1 (Flat.labels p)) -- namespace
abbrev bleep (z:Col G f) : Cell f := (z.1,Exterior.plaqEquiv.symm z.2.1)
lemma peal (u:Directions G f) (z:Col G f) : jet u z=Hypnos.tide u (bleep z) z.2.2:=by
    change dColor G f 1 (Flat.labels u) (z.1,z.2.1) z.2.2=dColor G f 1 (Flat.labels u) (z.1,plaqEquiv (bleep z).2) z.2.2; change _=dColor G f 1 _ (_, plaqEquiv (plaqEquiv.symm z.2.1)) _; rw [plaqEquiv.apply_symm_apply]

def purseK (_X:Coat T F)(w:Air f G): FreeResolvent.Active G F→ℝ :=fun i=>w (i.1.val,i.2)

lemma pore : plane (G:=G) S F *ᵥ purseK X w=jet (growSeed X w):=by
    let a:AxisChart G F:= FreeResolvent.profile F (purseK X w)
    have he:purseK X w=FreeResolvent.active F a:=rfl
    have ht:stretch (S:=S) F (0,a)= Flat.labels (growSeed X w):=by
       funext i; obtain ⟨q,hq⟩:= (Work.E03.poleEquiv f).surjective i; rw [← hq]
       have hz:= Work.F01.collect_vertical (S:=S) F a q
       change collect G (stretch (S:=S) F (0,a)) q= collect G (Flat.labels (growSeed X w)) q
       rw [hz,Flat.collected]; unfold growSeed; split; simp [*]; rfl
    unfold plane; rw [he,← Matrix.mulVec_mulVec,FreeResolvent.chart_flow,ht]
    funext i; exact congr_fun (FreeResolvent.component_mul (G:=G) _ _ i.2.2) (i.1,i.2.1)
variable {η α ε ν:ℝ}{p q : Clip}(H₀ : Towers.Diagonal S H H' T₀)
include H₀
lemma travel_match (hx:T.R.A0=T₀.A0) (h: Floor H p f η ν): (view G S H H' T₀)*ᵥ jet u= jet (route T u):=by
    have hf := h ; have hp := H₀.stays
    let U:= installed S.ratio T₀.A0
    have hT : psi S H H' T₀*d 1 c=(d 1 f)*U:=by
       unfold psi; simp only [Matrix.mul_assoc]; unfold U; rw [← Matrix.mul_assoc _ (H'.diagonal.acts c), hp]; simp only [← Matrix.mul_assoc, show H.dual_diag.acts f*H.diagonal.acts f=1 from mul_eq_one_comm.mp h.diagonalInv, Matrix.one_mul]
    have he i : parts G 1 (Flat.labels (route T u)) i= U*ᵥ parts G 1 (Flat.labels u) i := by
       funext p; obtain ⟨q,hq⟩:=(Work.E03.poleEquiv f).surjective p; rw [←hq]; change collect G (Flat.labels (route T u)) q i=_; rw [Flat.collected]
       unfold JointLoad.Heir.route JointLoad.Heir.main; rw [hx]; rfl
    funext i; unfold view; rw [show (FreeResolvent.tensor G _ *ᵥ jet u) i=_ from congr_fun (FreeResolvent.component_mul (G:=G) _ (jet u) i.2.2) (i.1,i.2.1)] -- perhaps pattern
    let z:=i.2.2
    change (psi S H H' T₀ *ᵥ ((d 1 c) *ᵥ parts G 1 (Flat.labels u) z)) _ =(d 1 f *ᵥ parts G 1 (Flat.labels (route T u)) z) _; rw [he,mulVec_mulVec,hT, mulVec_mulVec]
variable {η' ν':ℝ}
lemma factorKl (G:Gauge)(F:Tree.Forest S.ratio)(hz: Bid.Larger (G:=G) S)(h: Floor H p f η ν)(h':Floor H' q c η' ν')(hη:0<η)(hν:0<η') : (show Matrix (FreeResolvent.Slot G f (1+1)) (FreeResolvent.Slot G f (1+1)) ℝ from curtain G S H H' T₀)= (show Matrix (FreeResolvent.Slot G f (1+1)) _ ℝ from plane S F (G:=G))*(FreeResolvent.treeMatrix G S F H.metric)⁻¹*(plane S F (G:=G)).transpose :=by
    simpa only [curtain,FreeResolvent.treeInverse,FreeResolvent.resolve,zero_smul,add_zero] using (cutHead S F H hz h hη T₀ h' hν H₀).symm
end Fruit
end YM.Hypnos
#print axioms YM.Hypnos.Fruit.travel_match
#print axioms YM.Hypnos.Fruit.factorKl
#print axioms YM.Hypnos.Fruit.pore
