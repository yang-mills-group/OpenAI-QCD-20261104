import YM.Vern.Vines
set_option autoImplicit false
set_option maxHeartbeats 910000
noncomputable section
namespace YM.NativeV
open Function Set Filter Analysis
open scoped Topology BigOperators Classical
open Lobo Vern Finset
private lemma pick3(x:Lobo.Tri):x=0∨x=1∨x=2:=by fin_cases x<;>simp
variable {W X:Type}[AddCommGroup W][Module ℂ W][AddCommGroup X][Module ℂ X]
variable (C:Medal W)(J:Drift C X)(p f:ℝ)(T:Tri→Tri→W)(ht:Olive C p f T)
variable (V:Tri→X)(e:ℝ)
variable (V':Tri→Tri→X)(c:ℂ)(he:p≠f)(hN:Nation C J V' c)
set_option maxHeartbeats 1500000
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
local notation "G_" i:arg x:arg=> haze C J T i (strip C J i x)
include ht he hN

lemma ZK0(x y:Tri): G_ (0:Axis) (V' x y)=0:=by
     obtain ⟨h1,h2,h3,h4⟩:=race C J p f T ht he V' c hN; change haze C J T 1 (V' 1 0)=0 at h1; change haze C J T 2 (V' 2 0)=0 at h2; change haze C J T 0 (V' 0 0)=0 at h3; change haze C J T 0 (V' 1 1)+ haze C J T 0 (V' 2 2)=0 at h4
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl<;>  (rcases (show y=0∨y=1∨y=2 from pick3 y) with rfl|rfl|rfl) <;> simp only [spout,map_add,map_smul,show maybeQ 0=0 from rfl,show NativeV.sBeta 0=1 from rfl,show sAlpha 0=1 from rfl,hN.wax,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg,(show V' 0 1=V' 1 0 from hN.sym ..),(show V' 0 2=V' 2 0 from hN.sym ..),(show V' 1 2= V' 2 1 from hN.sym ..)]
     all_goals first| (ring; done)|linear_combination 8*h1|linear_combination 8*h2|linear_combination 8*h3|linear_combination 4*h4| (rw [hN.sym 0 1];linear_combination 8*h1)| (rw [hN.sym 0 2]; linear_combination 8*h2)
lemma ZK1(x y:Tri): G_ (1:Axis) (V' x y)=0:=by
     obtain ⟨h1,h2,h3,h4⟩:=race C J p f T ht he V' c hN; change haze C J T 1 (V' 1 0)=0 at h1; change haze C J T 2 (V' 2 0)=0 at h2; change haze C J T 0 (V' 0 0)=0 at h3; change haze C J T 0 (V' 1 1)+ haze C J T 0 (V' 2 2)=0 at h4
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl<;>  (rcases (show y=0∨y=1∨y=2 from pick3 y) with rfl|rfl|rfl) <;> simp only [spout,map_add,map_smul,show maybeQ 1=2 from rfl,show NativeV.sBeta 1=-1 from rfl,show sAlpha 1=-1 from rfl,hN.wax,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show roof 2 0= 1 from (by decide),show roof 2 1= 0 from (by decide),show roof 2 2= 2 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide),show τc 2 0= 1 from (by unfold τc charI; simp +decide),show τc 2 1= -1 from (by unfold τc charI; simp +decide),show τc 2 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg,(show V' 0 1=V' 1 0 from hN.sym ..),(show V' 0 2=V' 2 0 from hN.sym ..),(show V' 1 2= V' 2 1 from hN.sym ..)]
     all_goals first| (ring; done)|linear_combination 8*h1|linear_combination 8*h2|linear_combination 8*h3|linear_combination 4*h4| (rw [hN.sym 0 1];linear_combination 8*h1)| (rw [hN.sym 0 2]; linear_combination 8*h2)
lemma ZK2(x y:Tri): G_ (2:Axis) (V' x y)=0:=by
     obtain ⟨h1,h2,h3,h4⟩:=race C J p f T ht he V' c hN; change haze C J T 1 (V' 1 0)=0 at h1; change haze C J T 2 (V' 2 0)=0 at h2; change haze C J T 0 (V' 0 0)=0 at h3; change haze C J T 0 (V' 1 1)+ haze C J T 0 (V' 2 2)=0 at h4
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl<;>  (rcases (show y=0∨y=1∨y=2 from pick3 y) with rfl|rfl|rfl) <;> simp only [spout,map_add,map_smul,show maybeQ 2=1 from rfl,show NativeV.sBeta 2=1 from rfl,show sAlpha 2=-1 from rfl,hN.wax,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg,(show V' 0 1=V' 1 0 from hN.sym ..),(show V' 0 2=V' 2 0 from hN.sym ..),(show V' 1 2= V' 2 1 from hN.sym ..)]
     all_goals first| (ring; done)|linear_combination 8*h1|linear_combination 8*h2|linear_combination 8*h3|linear_combination 4*h4| (rw [hN.sym 0 1];linear_combination 8*h1)| (rw [hN.sym 0 2]; linear_combination 8*h2)
lemma ZK3(x y:Tri): G_ (3:Axis) (V' x y)=0:=by
     obtain ⟨h1,h2,h3,h4⟩:=race C J p f T ht he V' c hN; change haze C J T 1 (V' 1 0)=0 at h1; change haze C J T 2 (V' 2 0)=0 at h2; change haze C J T 0 (V' 0 0)=0 at h3; change haze C J T 0 (V' 1 1)+ haze C J T 0 (V' 2 2)=0 at h4
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl<;>  (rcases (show y=0∨y=1∨y=2 from pick3 y) with rfl|rfl|rfl) <;> simp only [spout,map_add,map_smul,show maybeQ 3=0 from rfl,show NativeV.sBeta 3=-1 from rfl,show sAlpha 3=1 from rfl,hN.wax,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg,(show V' 0 1=V' 1 0 from hN.sym ..),(show V' 0 2=V' 2 0 from hN.sym ..),(show V' 1 2= V' 2 1 from hN.sym ..)]
     all_goals first| (ring; done)|linear_combination 8*h1|linear_combination 8*h2|linear_combination 8*h3|linear_combination 4*h4| (rw [hN.sym 0 1];linear_combination 8*h1)| (rw [hN.sym 0 2]; linear_combination 8*h2)
omit hN
variable (hX:Spirit C J V e)
include hX
lemma TK0(x:Tri): G_ (0:Axis) (V x)=0:=by
     have h₀:haze C J T 3 (V 0)=0:=grain C J p f T ht V e he hX
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl <;> simp only [spout,map_add,map_smul,show maybeQ 0=0 from rfl,show NativeV.sBeta 0=1 from rfl,show sAlpha 0=1 from rfl,hX.cov,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg]
     all_goals try rw [h₀]
     all_goals ring
lemma TK1(x:Tri): G_ (1:Axis) (V x)=0:=by
     have h₀:haze C J T 3 (V 0)=0:=grain C J p f T ht V e he hX
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl <;> simp only [spout,map_add,map_smul,show maybeQ 1=2 from rfl,show NativeV.sBeta 1=-1 from rfl,show sAlpha 1=-1 from rfl,hX.cov,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show roof 2 0= 1 from (by decide),show roof 2 1= 0 from (by decide),show roof 2 2= 2 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide),show τc 2 0= 1 from (by unfold τc charI; simp +decide),show τc 2 1= -1 from (by unfold τc charI; simp +decide),show τc 2 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg]
     all_goals try rw [h₀]
     all_goals ring
lemma TK2(x:Tri): G_ (2:Axis) (V x)=0:=by
     have h₀:haze C J T 3 (V 0)=0:=grain C J p f T ht V e he hX
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl <;> simp only [spout,map_add,map_smul,show maybeQ 2=1 from rfl,show NativeV.sBeta 2=1 from rfl,show sAlpha 2=-1 from rfl,hX.cov,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg]
     all_goals try rw [h₀]
     all_goals ring
lemma TK3(x:Tri): G_ (3:Axis) (V x)=0:=by
     have h₀:haze C J T 3 (V 0)=0:=grain C J p f T ht V e he hX
     rcases (show x=0∨x=1∨x=2 from pick3 x) with rfl|rfl|rfl <;> simp only [spout,map_add,map_smul,show maybeQ 3=0 from rfl,show NativeV.sBeta 3=-1 from rfl,show sAlpha 3=1 from rfl,hX.cov,show roof 0 0= 0 from (by decide),show roof 0 1= 2 from (by decide),show roof 0 2= 1 from (by decide),show roof 1 0= 2 from (by decide),show roof 1 1= 1 from (by decide),show roof 1 2= 0 from (by decide),show τc 0 0= 1 from (by unfold τc charI; simp +decide),show τc 0 1= 1 from (by unfold τc charI; simp +decide),show τc 0 2= -1 from (by unfold τc charI; simp +decide),show τc 1 0= -1 from (by unfold τc charI; simp +decide),show τc 1 1= 1 from (by unfold τc charI; simp +decide),show τc 1 2= 1 from (by unfold τc charI; simp +decide), smul_eq_mul,one_mul,one_smul,neg_one_mul,neg_one_smul,map_neg,neg_neg]
     all_goals try rw [h₀]
     all_goals ring
end YM.NativeV
#print axioms YM.NativeV.TK0
#print axioms YM.NativeV.TK1
#print axioms YM.NativeV.TK2
#print axioms YM.NativeV.TK3
#print axioms YM.NativeV.ZK0
#print axioms YM.NativeV.ZK1
#print axioms YM.NativeV.ZK2
#print axioms YM.NativeV.ZK3
