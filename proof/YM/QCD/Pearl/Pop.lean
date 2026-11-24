import YM.QCD.Pearl.Creek
import YM.QCD.Runnel.Crest

/-! # summing momentum bill and the exact charged jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free RG Rudder Revolve Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {n : Side} {I J D : Type} {m j : ℕ} {η a b c : ℝ}

def railz (m : ℕ): Bloom m:=⟨[],fun _=>⟨[],⟨(0,1),by decide⟩⟩,0⟩
abbrev Shine:= Momentum×Momentum
abbrev twin (p : ℝ):Set Shine:= strip p ×ˢ strip p
structure Wall (p q:ℝ) (f:Shine→Bundle): Prop where
 d x (_:x∈ twin p): DifferentiableAt ℂ f x
 s x (_:x∈ twin p): ‖f x‖≤q
structure Package (η a b c:ℝ) (P : Plan j) (v:Train j) (G:I→Gleam)(U:J→Bloom 1)(V:D→Bloom 2): Prop where
 scale : 0<η
 psi : Wages (4*η) a G
 matchA : Shows G (fun _ t=> wood P t v)
 first : Fractal U (4*η) b
 second : Fractal V (4*η) c

section sum
variable {η c : ℝ}
lemma Wall.plus {u v: ℝ} {X Y : Shine→Bundle}(h:Wall η u X)(e:Wall η v Y):Wall η (u+v) (X+Y):= ⟨fun i p=> (h.d i p).add (e.d i p),fun i p=> (norm_add_le ..).trans (add_le_add (h.s i p) (e.s i p))⟩
lemma Wall.wave_c (F : I→ Shine→Bundle) (p:I→ℝ) (h : ∀ i,Wall η (p i) (F i)) (hs: Summable p)(hp:∑' i,p i≤c): Wall η c (fun z=>∑' i,F i z):=by
  refine ⟨Run.frosty F ((YM.Work.F07.stripOpen _).prod (YM.Work.F07.stripOpen _)) (fun i=>(h i).d) hs (fun i=>(h i).s), fun i v=> ?_⟩
  have he:=hs.of_nonneg_of_le (fun j=>norm_nonneg _) (fun j=> (h j).s i v)
  exact (norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum (fun j=> (h j).s i v) hs).trans hp)
end sum
variable (G:I→Gleam)(U:J→Bloom 1)(V:D→Bloom 2)(C : su.Color)
def v₁ (i : Axis)(x: Shine):=(∑' j, boom₁ C (G j) i x.1 x.2)+(∑' j, nil₁ C (U j) i x.1 x.2)
def v₂ (i : Axis)(x: Shine):= ((∑' j,boom₂ C (G j) i x.1 x.2)+(∑' j,yet₁ C (U j) i x.1 x.2))+(∑' j,yet₂ C (V j) i x.1 x.2)
def billPack (η a b c : ℝ)(G:I→Gleam)(U:J→Bloom 1)(V:D→Bloom 2):Prop:= Wages (4*η) a G ∧ Fractal U (4*η) b ∧ Fractal V (4*η) c
lemma vertex (h : 0<η)(a b c):∃ K S:ℝ,∀ (I J D:Type)(G:I→Gleam)(U:J→Bloom 1)(V:D→Bloom 2),
  billPack η a b c G U V→ ∀ i, Wall η K (v₁ G U C i)∧Wall η S (v₂ G U V C i):=by
  obtain ⟨K,hK,H⟩:=hill C h; obtain ⟨S,hS,E⟩:= knoll C h
  refine ⟨K*a+S*b,K*a+S*b+S*c,fun I J D G U V e i=>?_⟩
  obtain ⟨eA,eB,eC⟩:=e
  have ha:∑' j,K*(G j).rate (4*η)≤K*a:=by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left eA.cap hK
  have hb:∑' j,S*(U j).paid (4*η)≤S*b:=by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left eB.bill hS
  have hc:∑' j,S*(V j).paid (4*η)≤S*c:=by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left eC.bill hS
  constructor
  · exact (Wall.wave_c (fun j x=> boom₁ C (G j) i x.1 x.2) _ (fun j=> ⟨fun x _=> b₁d ..,fun x hx=> (H (G j) x.1 x.2 hx.1 hx.2 i).2.1⟩) (eA.val.mul_left K) ha).plus (Wall.wave_c (fun j x=>nil₁ C (U j) i x.1 x.2) _ (fun j=>⟨fun x _=>nil_d ..,fun x hx=> (E (U j) (railz 2) x.1 x.2 hx.1 hx.2 i).1⟩) (eB.bills.mul_left S) hb)
  exact ((Wall.wave_c (fun j x=>boom₂ C (G j) i x.1 x.2) _ (fun j=>⟨fun x _=>b₂d ..,fun x hx=> (H (G j) x.1 x.2 hx.1 hx.2 i).2.2⟩) (eA.val.mul_left _) ha).plus (Wall.wave_c (fun j x=>yet₁ C (U j) i x.1 x.2) _ (fun j=>⟨fun x _=>y₁d ..,fun x hx=> (E (U j) (railz 2) x.1 x.2 hx.1 hx.2 i).2.1⟩) (eB.bills.mul_left _) hb)).plus (Wall.wave_c (fun j x=>yet₂ C (V j) i x.1 x.2) _ (fun j=>⟨fun x _=>y₂d ..,fun x hx=> (E (railz 1) (V j) x.1 x.2 hx.1 hx.2 i).2.2⟩) (eC.bills.mul_left _) hc)

lemma billBand {p:Site n} (A:I→Sheet n)(Z:I→Site n→Bundle) (R) (h:HasSum A R)(he:∀ i, peel (A i)=cloud p (Z i)): peel R=cloud p fun j=>∑' i,Z i j:=by
  have ht: HasSum (fun i=>cloud p (Z i)) (peel R) := by simp_rw [← he]; exact (chamber n).hasSum h
  ext ⟨i,v⟩ ⟨j,w⟩; unfold cloud; rw [rr]; split
  all_goals
   let F : Sheet n→ₗ[ℂ] ℂ:={toFun:=fun K=>K (i,v) (j,w),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
   have hh:= F.toContinuousLinearMap.hasSum ht
  next H=>
    let L : Sheet n→ₗ[ℂ] Bundle:={toFun:=fun K=> Run.cell K i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
    have hp:= L.toContinuousLinearMap.hasSum ht
    dsimp only; rw [show (∑' l, Z l (i-p))=Run.cell (peel R) i j from ?_]; rfl
    refine HasSum.tsum_eq ?_; rw [show (fun l=>Z l (i-p))= (fun l=> L.toContinuousLinearMap (cloud p (Z l))) from ?_]; exact hp
    funext l; ext a b; change _=cloud p _ _ _; rw [cloud,rr,if_pos H]
  next H=>
    rw [show peel R (i,v) (j,w)=_ from hh.tsum_eq.symm];
    simp_rw [show ∀ l:I,F.toContinuousLinearMap (cloud p (Z l))=0 from fun l=> by change cloud p _ _ _= _; rw [cloud,rr,if_neg H],tsum_zero]

def totals (C : su.Color)(X:I → Gleam)(n:Side)(p : Weather n) : Sheet n := ∑' j,silo C 0 (X j) p
def reachouts (C : su.Color)(V:I→Bloom m)(n:Side)(p:Weather n):= ∑' j,silt C 0 (V j) p
def extent (C : su.Color)(G:I→Gleam)(U:J→ Bloom 1)(V:D→Bloom 2)(n : Side)(x:Weather n) := totals C G n x+reachouts C U n x+reachouts C V n x
variable {G U V} {P : Plan j}{v:Train j}
lemma dawn (h:Package η a b c P v G U V)(n:Side) : extent C G U V n 0=unbarred v n:=by
  have hp (i:I): silo C 0 (G i) (0:Weather n)=(G i).dept 0 1:=by unfold silo; rw [amass0]; rfl
  unfold extent totals reachouts; simp_rw [hp, low_silt C 0 _ (show 0<1 by decide), low_silt C 0 _ (show 0<2 by decide),tsum_zero, add_zero,(h.matchA n 0 1).tsum_eq]; exact bare_this ..
end YM.QCD.Pearl
