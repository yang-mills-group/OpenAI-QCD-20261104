import YM.QCD.Brick.Arrow
/-! # actual Affine-moment invoice at leading motion of the input -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {f c : Side}{j k N:ℕ}(F:Flight j k)(h:f.val=c.val*F.L.val){p b t x y A u:ℝ}
local notation "L"=> Modes f N
variable (o:Site f)
abbrev FormN (f:Side)(N :ℕ):= Matrix (Modes f N) (Modes f N) ℂ
-- stamp regardless of flavor diagonality
abbrev Note (N:ℕ):=Lat.Fiber × Flavor N
def signN (M:FormN f N)(x y : Note N)(i j : Site f):ℂ:= shine o i * shine o j * M (placeQ i x) (placeQ j y)
def flowN (M:FormN f N)(x y : Note N)(w:SampleX):ℂ:= ∑ i,∑ j, mark o w i j * signN o M x y i j
abbrev staff (X:Kit.Rail f c)(z: Accent N):= fun i=>loomQ o X i z
def apple (X:Kit.Rail f c)(N:ℕ):Crate f N→ₐ[ℂ] Crate c N:=changeVars (powerF X)
lemma shim (X:Kit.Rail f c)(z: Accent N)(x:Site f):staff o X z (heel o x)= shine o x • apple X N (atom (pitchQ x z)):=by
  unfold staff heel loomQ shine; rw [Quarry.occ_rays,route_end,wrap_lift,add_sub_cancel]; rfl
lemma mode_sum {S:Type*}[AddCommMonoid S](Q:L→S): (∑ i:L,Q i)=∑ q:Note N,∑ x:Site f,Q (placeQ x q):=by
   let E:L≃ Note N × Site f:={ toFun:=fun i=>((i.1.2,i.2),i.1.1),invFun:=fun x=> placeQ x.2 x.1,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl }
   rw [← Equiv.sum_comp E.symm,Fintype.sum_prod_type]; rfl
lemma born (M: FormN f N)(X:Kit.Rail f c) : apple X N (form M)=∑ i:Note N,∑ j:Note N,∑ u:Site f,∑ v:Site f, signN o M i j u v • (staff o X (Sum.inl j) (heel o v)*staff o X (Sum.inr i) (heel o u)):=by
   unfold form; simp only [map_sum,map_smul,map_mul]; rw [mode_sum]; apply sum_congr rfl; intro i _; simp_rw [mode_sum]; rw [sum_comm]; apply sum_congr rfl; intro j _; refine sum_congr rfl fun l _=> sum_congr rfl (fun k hk=>?_); rw [shim,shim,smul_mul_smul_comm,smul_smul]; unfold signN; obtain h|h:= shines o l<;> obtain hk|hk:=shines o k<;> rw [h,hk]<;> simp <;> try rfl
lemma emptyApple {D:Type*}[Fintype D](X Y:Cover → Alg D)(u v:Note N)(M:FormN f N)(hz:flowN o M u v none=0): ∑ i,∑ j,signN o M u v i j • (X 0*Y 0)=0:=by simp_rw [← sum_smul]; unfold flowN Stew.mark at hz; simp only [Option.elim,one_mul] at hz; rw [hz,zero_smul]
                                                                            
def dazzle (n: Bool)(X Y:Cover→ Alg (Keys c N))(x y:Cover):= if n then blossom X Y x y else X 0*Y 0
def lights (n:Bool)(M: FormN f N) :Prop := ∀ p q,flowN o M p q none=0 ∧ (n → ∀ v, flowN o M p q (some v)=0) -- Lean coerces Bool
lemma friend (X Y: Cover→ Alg (Keys c N))(i j:Note N)(b:Bool)(M:FormN f N)(he:lights o b M): ∑ x,∑ y,signN o M i j x y • dazzle b X Y (heel o y) (heel o x)=0:=by
   unfold dazzle; split
   · have hx(y: Cover):eBeam X y*Y 0=∑ a,(y a:ℂ) • (gust X a 0*Y 0):=by unfold eBeam affineD; rw [sum_mul]; simp_rw [smul_mul_assoc]
     have hy(y:Cover):X 0*eBeam Y y=∑ a,(y a:ℂ) • (X 0*gust Y a 0):=by unfold eBeam affineD; rw [mul_sum]; simp_rw [Algebra.mul_smul_comm]
     unfold blossom; simp_rw [hx,hy,smul_add,sum_add_distrib,Finset.smul_sum,smul_smul]
     let W:=signN o M i j; have hh (p: Bool)(z:Axis)(U: Alg (Keys c N)):(∑ k,∑ l, (W k l * mark o (some (z,p)) k l) • U)=0:=by simp_rw [mul_comm (W _ _),← sum_smul]; exact (by rw [show (∑ x:Site f,_) = _ from (he i j).2 (by assumption) (z,p),zero_smul]) -- ambiguous
     have ht : (∑ k:Site f,∑ l: Site f, ∑ z:Axis,(W k l * mark o (some (z,true)) k l) • (gust X z 0*Y 0))=∑ z:Axis,∑ k,∑ l,(W k l*mark o (some (z,true)) k l) • (gust X z 0*Y 0) := windSum (fun z k l=>(W k l* mark o (some (z,true)) k l) • (gust X z 0*Y 0))
     change (∑ x,∑ y,W x y • (X 0*Y 0)) + (∑ x,∑ y,∑ z:Axis, (W x y * mark o (some (z,true)) x y) • (gust X z 0*Y 0)) + (∑ x,∑ y,∑ z:Axis,(W x y *mark o (some (z,false)) x y) • (X 0*gust Y z 0))=_
     rw [ht, windSum (fun z k l=>(W k l*mark o (some (z,false)) k l) • (X 0*gust Y z 0)),show (∑ x,∑ y,W x y • (X 0*Y 0))=0 from emptyApple o X Y i j M (he i j).1]; simp_rw [hh]; simp
   exact emptyApple o X Y i j M (he i j).1
where windSum (g:Axis→ Site f→ Site f→ Alg (Keys c N)) : ∑ i,∑ j,∑ k, g k i j=∑ k,∑ i,∑ j,g k i j:=by rw [sum_comm (f:=fun k i=>∑ j,g k i j)]; exact sum_congr rfl fun i _=> sum_comm
end YM.QCD.Brick
