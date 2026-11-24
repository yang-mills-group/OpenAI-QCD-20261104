import YM.QCD.Fold.Dawn
/-! # exact short sale on twisted architecture. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden YM.Next.Free
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{G:Ratio C F}{Q: Ratio c f}{I J:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
variable {D b B:ℕ}
open Collum
variable (S:Collum f F (Site c) (Site C) D)(L:Window c C D){A:Therm (Site c) Q S.small}{K:Therm (Site C) G S.big}{T:Land F (Site C) (Site C)}{Y:Pays F (Site C) (Site C)}{M:Grid F → ArrayL (Site C) (Site C)}{m:Grid f →ArrayL (Site c) (Site c)}{a e r:ℝ}
-- explicit matrix cell through stream action ν.^
lemma leftH (X:Sheet C)(x:Site C→ℂ)(i j):cell ((stream L x)ᴴ*X) i j =∑ k∈parcel L.cut i, (star (x k)) • cell X k j:=by
   rw [cell_mul, Shingle.parcel,sum_filter]; refine sum_congr rfl fun k _=>?_; by_cases hv:L.cut k=i
   · rw [show cell ((stream L x)ᴴ) i k=star (cell (stream L x) k i) from rfl,show cell (stream L x) k i=x k • 1 from ?_,if_pos hv,star_smul,star_one,Matrix.smul_mul,one_mul]; ext u v; simp [Run.cell, stream,Matrix.one_apply,hv,mul_ite]
   rw [if_neg hv, show cell ((stream L x)ᴴ) i k=0 from (by change star (cell (stream L x) k i)=_; rw [show cell (stream L x) k i=0 from (by ext u v; simp [Run.cell, stream,hv]),star_zero]),zero_mul]
lemma rightH (X:ArrayL (Site c) (Site C))(x:Site C→ℂ)(i j):cell (X*stream L x) i j=∑ k∈parcel L.cut j, x k • cell X i k:=by
   rw [cell_mul,Shingle.parcel,sum_filter]; refine sum_congr rfl fun k _=>?_; by_cases hv:L.cut k=j
   · rw [if_pos hv, show cell (stream L x) k j=x k • 1 from ?_,Matrix.mul_smul,mul_one]; ext u v; simp [Run.cell,stream,Matrix.one_apply,hv,mul_ite]
   rw [if_neg hv, show cell (stream L x) k j=0 from by ext u v; simp [Run.cell, stream,hv],mul_zero]
lemma porting (X:Sheet C)(x:Site C→ℂ)(i j):cell ((stream L x)ᴴ*X*stream L x) i j=∑ k∈parcel L.cut i,∑ m∈parcel L.cut j,(star (x k)*x m) • cell X k m:=by
   rw [rightH]; simp_rw [leftH,smul_sum,smul_smul,mul_comm (x _)]; rw [Finset.sum_comm]
variable (Hb:Receives S M m)(hp:Pack S.big S.big a e b M r T Y)(hf:Held G K K T) (ht: ∀ i j,S.pi i=S.pi j → ∃ w z,S.salt (Collum.pin Q) w (fun _=>1) z A K ∧ Warrant (raise G w) z 1 ∧ K.shiftP w i=j) (hk: 4*B+3<f.val)
lemma shade_sale (x i j: Site C)(G:Bundle): sale x i j G=(if i=x then (2:ℂ)⁻¹ • G else 0)+(if j=x then (2:ℂ)⁻¹ • G else 0):=by unfold sale; split_ifs<;> first | grind | (simp only [add_mul,add_smul,one_mul,zero_mul,zero_smul])
lemma axisR {X:Site C×Site C→Bundle} (p:Site C)(i j:Site c):
 (∑ k∈parcel S.pi i,∑ m ∈ parcel S.pi j, ite (k=p) (X (k,m)) 0)= if i=S.pi p then ∑ m∈parcel S.pi j,X (p,m) else 0:=by
   rw [Finset.sum_comm]; by_cases h:i=S.pi p
   · rw [if_pos h]; exact sum_congr rfl fun a _=> by rw [Finset.sum_ite_eq',if_pos (by rw [h]; simp)] -- lemma
   rw [if_neg h]; exact sum_eq_zero fun k _=> sum_eq_zero fun m hv=> if_neg (fun he=> h ((posted ..).1 hv |>.symm.trans (congr_arg S.pi he)))
include Hb hp hf ht hk
-- specializes movement law. batches ratio only sets endpoint anchors, may differ
lemma forge (G':Ratio C F)(Q':Ratio c f)(hx : S.pi=L.cut)(he:(∀ i,S.big i=G'.embed i))(hv:∀ i,S.small i=Q'.embed i)(U:Grid f)(x:Site C)(hA:0<a):
   batch Q' (S.cloud T b B) (S.pi x) none B (settled U)= (stream L S.orient)ᴴ* batch G' T x none B (settled (S.T.links U))* stream L S.orient:=by
   apply whist; intro i j
   simp_rw [porting, stack, chipK, ←hx, ← hv, S.nest, ← he, shade_sale]; let p:=x
   let a i j:=spoon T (S.big x) B i j (settled (S.T.links U)); let X (i:Site C×Site C):= (2:ℂ)⁻¹ • S.rim i.1 i.2 • a i.1 i.2
   simp only [smul_add,smul_ite,smul_zero,sum_add_distrib]
   have hz i j : (star (S.orient i)*S.orient j) • ((2:ℂ)⁻¹ • a i j)=X (i,j):=smul_comm ..
   rw [Finset.sum_comm (s:=parcel S.pi i) (f:=fun k m=>ite (m=p) ((star (S.orient k)*S.orient m) • ((2:ℂ)⁻¹ • a k m)) 0)] -- goal match reducible
   have hm i:= forks S x i U ht Hb hf hp hk hA
   simp_rw [show ∀ i j, (star (S.orient i)*S.orient j) • ((2:ℂ)⁻¹ • spoon T (S.big x) B i j (settled (S.T.links U)))=X (i,j) from hz,hz]; dsimp only [p]; rw [show (∑ k∈parcel S.pi i,∑ m∈parcel S.pi j, ite (k=x) (X (k,m)) 0)= _ from axisR S x i j, show (∑ k ∈ parcel S.pi j,∑ m∈parcel S.pi i,ite (k=x) (X (m,k)) 0)= _ from axisR S (X:=fun p=>X p.swap) x j i]; unfold X; simp_rw [← smul_sum]; dsimp only at hm ⊢
   apply congr_arg₂ (·+·)
   · split_ifs with H; rw [H,(hm _).1]; rfl
   split_ifs with H; rw [H,(hm _).2]; rfl; rfl
end YM.QCD.Folding
