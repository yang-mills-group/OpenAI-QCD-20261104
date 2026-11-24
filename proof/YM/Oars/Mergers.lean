import YM.Oars.Planetaria
import YM.Cardinal.Beau
/-!
 # Anchor groups prepurchase.Height-compatible surface sum and conversion. Option multiplicity & rate after-L.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)
local notation "M"=> Ribbon.ample N I
variable (Y: Ruby.Hue c (ample N I) J)(F: Patron.Rail c (ample N I) U)
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "d!"=> withdraw N p θ
local notation "T!"=> Trail Y F t
namespace Stags
open Card Card.Iris
open Kit Kites ConnectedActivityE6 Pressure
variable {D: I→Type}
noncomputable def unionL (Y:∀ i, Reel c N I (D i)): Reel c N I (Σ i,D i):=⟨fun i=> (Y i.1).addr i.2, fun i=> (Y i.1).z i.2, fun i V=>(Y i.1).mark i.2 V⟩
lemma gatherings (Y:∀ i, Reel c N I (D i))(h:∀ i,(Y i).Book p q): (unionL N Y).Book p q:=⟨fun i=>(h i.1).stays _,fun i=> (h i.1).stamp _, fun i=> (h i.1).permit _,fun i=> (h i.1).room _,fun i=> (h i.1).stage _,fun i=> (h i.1).tint _⟩
lemma sigmaBud (f:(Σ i,D i)→ℝ)(g:I→ℝ)(h:∀ i,SumBudget (fun j:D i=> f ⟨i,j⟩) (g i))(hp:SumBudget g a): SumBudget f a:=by
    refine budget_fiberwise Sigma.fst (fun ⟨i,j⟩=> (h i).1 _) (fun i s hv=>?_) hp; let S:= Sigma.mk (β:=D) i
    have hS: Function.Injective S:= fun _ _ h=> eq_of_heq (Sigma.mk.inj_iff.mp h).2; choose p hp using (show ∀ i':s,i'.val∈ Set.range S from fun ⟨⟨k,j⟩,hj⟩=>by dsimp only; let Z:= Sigma D; have H:k=i:= hv _ hj; subst k; exact ⟨_,rfl⟩) -- dependent hv after gene problematic
    let t:= s.attach.image p; have ht:s=t.image S:=by ext v; constructor; intro hi; let x:↥s:= ⟨v,hi⟩; exact mem_image.mpr ⟨p x,mem_image_of_mem p (mem_attach ..),hp _⟩; intro H; obtain ⟨u,hu,rfl⟩:=mem_image.mp H; obtain ⟨u,hu,rfl⟩:=mem_image.mp hu; rw [hp]; exact u.2
    exact (congr_arg (fun z=> ∑ i∈z, f i) ht).trans_le ((sum_image hS.injOn).trans_le (budget_sum (h i) t)) -- args
-- use anchored.Foot prices
local notation "sp"=>SumBudget
open Footprint
variable (b M₁:ℕ)(he:Fires p M₁)
noncomputable def bonus (u:ℕ)(ε:ℝ):ℝ:= Footprint.payment 1 (4*u+4) 0 ε 1 (M₁:ℝ) 0 0 -- v bounds
variable (X: (Σ i,D i)→ Support c)(f:(Σ i,D i)→ℝ) (hp:∀ i, p i.1∈ X i)(hg:∀ i:I,Ac.Hit (fun z=>X (⟨i,z⟩: Sigma D)) b (fun z=> f ⟨i,z⟩) v A)
local notation "Z"=> Sigma D
include hp he hg
lemma claims (hV:0≤A)(V:Site c) :
   SumBudget (fun i:Z=> if p i.fst=V then f i * Real.exp (v*coverNumber b (X i)) else 0) (M₁*A):=by
   let s: Finset I:=univ.filter (fun i=> p i=V); have hc : (s.card:ℝ) ≤ M₁:=by exact_mod_cast he V
   let g(i:I):= if p i=V then A else 0; refine sigmaBud _ g ?_ ?_; swap
   · refine ⟨fun i=>ite_nonneg hV le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]; unfold g; rw [← sum_filter,sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hc hV
   intro j; obtain ⟨z,h⟩:∃ z:ℝ,z=A:=⟨A,rfl⟩ -- edit
   unfold g; split
   next H=>
      exact Iris.hit_collect (p j) (fun z=> X (⟨j,z⟩: Sigma D)) (fun z=> f ⟨j,z⟩) (fun z=>hp ⟨j,z⟩) (hg j)
   next H=> exact ⟨fun _=>le_rfl, summable_zero,by simp⟩
lemma welfare (hh:0≤A)(h:reserve v a 1 t): Ac.Hit X b f a (bonus M₁ b t*A) :=by
     let P:=fun i:Z=>p i.1; have ht(i:Z):0 ≤ f i:=by have ht:=Iris.hit_collect (p i.1) _ _ (fun j:D i.1=>hp ⟨_,j⟩) (hg i.fst); exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 (ht.1 i.snd)
     have h1:= assigned (v:=0) (v':=1) (id (α:=Site c)) 1 (by intro s; simp) P f ht (fun i=>coverNumber b (X i)) X (claims p b M₁ he X f hp hg hh) (4*b+4) 0 b (fun i x h=> (Corona.extent _ b h (hp i)).trans (by change _ ≤ (4*b+4)*(1+_); nlinarith only [Nat.zero_le (coverNumber b (X i)),Nat.zero_le b])) (fun i=>by simp) zero_le_one h f ht (fun i=>by simp)
     apply Eq.mp (congr_arg (fun b=>Ac.Hit X _ _ a b) ?_) h1; unfold bonus Footprint.payment degreeIncome; simp only [mul_zero,Real.exp_zero]; ring
end Stags
end YM.MassiveQCD.Plate
