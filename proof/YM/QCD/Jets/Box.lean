import YM.QCD.Jets.Story
/-! # short and long seats budgets pointwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y:ℝ}{l:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

abbrev sumX (i:Support f):=∑ x:Site f,∑ y:Site f,P.Y x y i
def sumS (r:ℕ)(i: Support f):=∑ x:Site f,∑ y:Site c,if i∈ Fork.satZip x r then P.W x y i+P.B0 y x i else 0

def fingers (F:ℕ):ℝ:= F * (Fintype.card Fiber:ℝ)
lemma rowsSum (p:Side) (F:ℕ)(X:Site p→ℝ):∑ i:Modes p F,X (headF i)= fingers F * ∑ j:Site p,X j:=by
  change ∑ i: (Site p × Fiber) × Flavor F,_=_; rw [Fintype.sum_prod_type]; simp_rw [headF,Fintype.sum_prod_type]; simp only [sum_const,card_univ,Flavor,Fintype.card_fin,nsmul_eq_mul,fingers]; rw [mul_sum]; exact sum_congr rfl (fun i _=>by ring_nf; norm_num [Fiber,Pinor,Hue])
lemma paddleB (r:ℕ) (s:Support f)(c:ℝ)(M:A→Modes f F→ℝ) (X: Site f→Site f→ℝ) (hc:∀ i j,M i j≤ X (headF i) (headF j)): ∑ i:A,∑ j,M i j ≤ fingers F^2*(∑ i:Site f,∑ j, X i j):=by
  apply le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> hc i j)))
  apply le_of_eq; simp_rw [show ∀ i:Modes f F,(∑ j:Modes f F,X (headF i) (headF j))=_ from fun i=> rowsSum f F (X (headF i))]
  rw [← mul_sum,rowsSum f F (fun i=> ∑ j,X i j)]; ring
lemma padS (p:A→B→ℝ)(X: Site f→Site c→ℝ) (hc:∀ i j,p i j≤ X (headF i) (headF j)): ∑ i:A,∑ j,p i j≤fingers F^2*(∑ i:Site f,∑ j,X i j):=by
  apply le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> hc i j)))
  apply le_of_eq; simp_rw [show ∀ i:Modes f F,(∑ j:Modes c F,X (headF i) (headF j))=_ from fun i=> rowsSum c F (X (headF i))]
  rw [← mul_sum,rowsSum f F (fun i=> ∑ j,X i j)]; ring

lemma queen (t:ℝ)(b:ℕ)(U:Pulse f)(hv:U∈Kingdom f δ)(s:Support f): ∑ i:A,∑ j:A, ‖ship P.X s U i j‖≤ fingers F^2*sumX P s:=by
  apply paddleB b s t; intro i j; rw [hook_eq]; split
  · exact (Cost.north ..).trans ((P.X0.crop (headF i) (headF j) s).2.2.2.1 _ hv)
  rw [norm_zero]; exact (P.X0.crop ..).1
lemma sailS (U:Pulse f)(hv:U∈Kingdom f δ)(b:ℕ)(s:Support f): ∑ i:Keys f F,∑ j:Keys c F,‖longP P.Z P.V b U s i j‖ ≤ fingers F^2*sumS P b s:=by
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type,longP,foamRL,foamLR,norm_zero, Finset.sum_const_zero,zero_add,add_zero]
  rw [← sum_add_distrib]; simp_rw [←sum_add_distrib]
  apply padS
  intro i j; rw [foamI,foamR]; unfold headF
  by_cases ht:s ∈satZip i.1.1 b; swap; · by_cases h:i.2=j.2 <;> simp [ht,h] -- likely issues
  by_cases H:i.2=j.2
  · simp only [ht,H, if_true]; exact add_le_add ((Cost.north ..).trans ((P.Z0.crop (headF i) (headF j) s).2.2.2.1 _ hv)) ((Cost.north ..).trans ((P.V0.crop (headF j) (headF i) s).2.2.2.1 _ hv))
  simp only [ht,H,Ne.symm H, if_true,if_false, norm_zero,add_zero]; exact add_nonneg (P.Z0.crop ..).1 (P.V0.crop ..).1

lemma rate_ok (p : R)(hx:0<x)(hy:0<y):0 < rateF c f F x y p:=by
  rcases splits_index p with ⟨s,rfl⟩|⟨s,rfl⟩ <;> simp only [rateF,wagesB,wagesA, hx,hy]

-- costs in P1 norm

def terra (F:ℕ)(b:ℕ)(x y:ℝ): Tr f→ℝ:=Sum.elim (fun i=> fingers F^2*sumX P i*x⁻¹^2) fun i=> fingers F^2*sumS P b i*(y*x⁻¹)
lemma licence (U:Pulse f)(hv:U∈Kingdom f δ)(hx:0<x)(hy:0<y)(b:ℕ)(i: Tr f): Ledge.Pledge (rateF c f F x y) (mapQ P.X P.Z P.V b i U) (terra P F b x y i):=by
   cases i
   next i=>
    change Pledge _ (pond _ _) _
    apply (parent _ _ (fun i=>rate_ok i hx hy) _).bumps
    unfold Ledge.pawn; simp only [met,pet,ha,rateF,wagesA,←sum_mul]
    rw [← sq]; exact mul_le_mul_of_nonneg_right (queen P x b U hv i) (sq_nonneg _)
   next i=>
    apply (prices (longP P.Z P.V b U i) _ (fun i=> rate_ok i hx hy) (head A B) (tail A B)).bumps
    unfold barksP; simp only [rateF,wagesA,wagesB,←sum_mul]; exact mul_le_mul_of_nonneg_right (sailS P U hv b i) (by positivity)
end YM.QCD.Jets.Sun
