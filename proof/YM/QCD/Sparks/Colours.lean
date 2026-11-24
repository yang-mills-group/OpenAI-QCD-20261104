import YM.QCD.Sparks.Gale

/-! # Leading color module for each anchor at a fixed cover cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Eyrie Quarry Tree RG Precision Rudder Flume Pine Finset Set Exterior
open YM.Further.PhysicalPeriodLimitF933 Macrame Jacobi Stationary Tavern
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side} {k m M:ℕ}

abbrev Stock := Cover × Angle
abbrev Rim (k:ℕ):= Cover × (Fin k→Stock)
def raise (l:Rim k)(b:Fin k→ su.ColorIndex) : Tilt k:= (l.1, fun i=> ((l.2 i).1,(l.2 i).2,b i))
def graduated (K:Typewriter k)(s:Rim k)(Y:Fin k→su.Color):= ∑ a:Fin k→su.ColorIndex,(((∏ i, Y i (a i)):ℝ):ℂ) • K (raise s a)
def Glow (K:Typewriter k):Prop:= ∀ s u (v:Fin k→su.Color), graduated K s (fun i=> su.adjoint u (v i))=touch (colour u)*graduated K s v*star (touch (colour u))
lemma standing (p : Tilt k): AtMap n p↔(Lattice.lift (wrap n p.1)=p.1∧∀ i,Lattice.lift (wrap n (p.2 i).1)=(p.2 i).1):=by
  refine ⟨fun h=>⟨congr_arg Prod.fst h,fun i=> congr_arg (fun s:Tilt k=> (s.2 i).1) h⟩,fun ⟨h,H⟩=>?_⟩; exact Prod.ext h (funext fun i=> Prod.ext (H i) rfl)
lemma rub {p:Rim k} (a b:Fin k→su.ColorIndex) : AtMap n (raise p a)↔ AtMap n (raise p b):= by rw [standing,standing]; rfl
lemma cR (i : Row n): (1:Sheet n) i i=1:= Matrix.one_apply_eq ..

def hybrid (v:su.Color) (x:Site n)(a:Angle): Cnr n:=fun i=> if i.1=x ∧ i.2.1=a then v i.2.2 else 0
lemma hybrids (x:Site n)(a:Angle)(b:su.Color): hybrid b x a=∑ z,b z • Push.Uniform.bolt (x,a,z):=by
  funext ⟨i,t,k⟩; unfold hybrid; rw [Finset.sum_apply]; split_ifs with h
  · change i=x ∧ t=a at h; rw [h.1,h.2]; simp [Push.Uniform.bolt,Pi.single_apply]
  simp [Push.Uniform.bolt,Pi.single_apply,h,← and_assoc]
lemma stained_lock (u:su.El)(x:Site n)(a:Angle)(B:su.Color): stain u (hybrid B x a)=hybrid (su.adjoint u B) x a:=by
  apply (arm su n 1).injective; funext ⟨v,i⟩; simp only [stain,ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,(arm su n 1).apply_symm_apply]
  have hp (b): arm su n 1 (hybrid b x a) (v,i)=if v=x∧i=a then b else 0:=by ext j; split_ifs with h <;> simp [arm_apply,hybrid,h]
  change su.adjoint u ((arm su n 1) _ (v,i))=_; simp_rw [hp]; split <;> simp_all

def palette (s:Rim k)(n:Side)(v:Fin k→su.Color)(i:Fin k): Cnr n:= hybrid (v i) (wrap n (s.2 i).1) (s.2 i).2
lemma painted {s:Rim k} (a:Fin k→su.ColorIndex) (h:AtMap n (raise s a)) (F:trackG n) (v:Fin k→su.Color):
    graduated (design F) s v= (occ (0:Site n) s.1) • Run.cell (surge F (palette s n v)) 0 (wrap n s.1):=by
  let z:= wrap n s.1
  have he : (Lattice.lift z)=s.1:= ((standing _).mp h).1
  have hp : palette s n v=(fun i=>∑ a:su.ColorIndex, v i a • Push.Uniform.bolt (wrap n (s.2 i).1,(s.2 i).2,a)):=funext fun _=>hybrids ..
  let M:=iteratedFDeriv ℝ k F 0
  have hz : surge F (palette s n v)=∑ p:Fin k→su.ColorIndex,(∏ i,v i (p i)) • M fun i=>Push.Uniform.bolt (wrap n (s.2 i).1,(s.2 i).2,p i):=by
    rw [surge,hp,blast]; exact sum_congr rfl fun p _=> M.toMultilinearMap.map_smul_univ _ _
  change graduated _ _ v=_ • Run.cell (surge F _) (0:Site n) z
  let L := cellC (0:Site n) z
  change _=_ • L (surge F (palette s n v)); rw [hz,map_sum]; unfold graduated; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun p _=> ?_
  rw [design,if_pos ((rub a p).1 h),normedD,show lift (down n (raise s p)).1=s.1 from he, smul_comm ((↑(_ : ℝ)):ℂ)]
  have hm := map_smul (L.restrictScalars ℝ) (∏ i,v i (p i)) (M fun i=>Push.Uniform.bolt (wrap n (s.2 i).1,(s.2 i).2,p i)); congr 1

lemma buys (F:trackG n)(h:Priest F)(k): Glow (@design n k F):=by
  intro s u v
  by_cases he : ∃ p,AtMap n (raise s p)
  · obtain ⟨p,hp⟩:=he
    rw [painted p hp,painted p hp, show palette s n (fun i=>su.adjoint u (v i))=(stain u)∘(palette s n v) from funext fun i=> (stained_lock u ..).symm,surge_stain h]
    unfold aura; rw [← gyro_id,gyro, Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [graduated,design]; push Not at he; simp only [if_neg (he _),smul_zero,Finset.sum_const_zero,mul_zero,zero_mul]
lemma lim_color {S : SparkMesh} {F:S.Field} {K:Typewriter k}{m:ℕ→ℕ}{r A:ℝ}(h:Exhibit S F k r A m K)(hk:∀ i,Priest (F i)):
    Glow K:=by
  intro s u v; let T (i): Tilt k→Bundle:= design (F (m i));
  have he v : Tendsto (fun i=> graduated (T i) s v) atTop (𝓝 (graduated K s v)):=tendsto_finsetSum _ fun i _=> (h.shape (raise s i)).const_smul _ -- names
  let A:=touch (colour u); apply tendsto_nhds_unique (he _) ; have hy: (fun i=> A*graduated (T i) s v*star A)=(fun i=> graduated (T i) s (fun j=> su.adjoint u (v j))):=funext fun i=>(buys _ (hk (m i)) k s u v).symm
  rw [← hy]; exact (tendsto_const_nhds.mul (he v)).mul tendsto_const_nhds
end YM.QCD.Sparks
