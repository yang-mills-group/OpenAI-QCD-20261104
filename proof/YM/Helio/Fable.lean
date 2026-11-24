import YM.Helio.Week
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
variable (G:Silo c)(x:Axis){j' :ℕ}
section fold
open scoped Classical
variable (V:Grid c)(p q:Site c)(Y:Bundle)
def clap (A:Bundle): Bundle:=J0*star A*J0
def clapL: Bundle →L[ℝ] Bundle:= LinearMap.toContinuousLinearMap { toFun:=clap,map_add':=fun i j=>by unfold clap; rw [star_add, mul_add,add_mul],map_smul':=fun z i=>by unfold clap; rw [star_smul, star_trivial,Matrix.mul_smul,Matrix.smul_mul]; rfl }
lemma scaleF : foldH (Stew.block p q Y)=Stew.block q p (clap Y):=by
    apply Sway.whist; intro i j; unfold foldH; nth_rw 2 [← terraJ (D:= Site c)]; unfold terraL; rw [cell_ride_right,cell_ride_left,Equiv.refl_apply, cell_flip,pairBl,pairBl]; simp only [Equiv.refl_apply]; split; next h=> rw [if_pos h.symm]; rw [cT]; rfl
    next h=> rw [if_neg (mt And.symm h),star_zero, mul_zero,zero_mul]
lemma tissue (A:Sheet c): star (Lat.shift 0 V x)*foldH A-foldH A*star (Lat.shift 0 V x) = - foldH (Lat.shift 0 V x*A-A*Lat.shift 0 V x):=by
    let W:= star (Lat.shift 0 V x); let J:=chirality c; have h:W*J=J*W:= (Lat.back_spin g5 0 V x).eq -- check
    change W*(J*star A*J)-(J*star A*J)*W= -(J*star _ * J); rw [star_sub,star_mul,star_mul]; change _= -(J*(star A*W-W*star A)*J); rw [← mul_assoc, ← mul_assoc W J, h,mul_sub,sub_mul]; simp only [Matrix.mul_assoc]; rw [← h]; rw [neg_sub]
lemma flora (i:Site c)(g:Frame c): touch (Lat.colour (g i))*J0=J0*touch (Lat.colour (g i)):= (interlace ..).eq
lemma pigments (g:Frame c): clap (touch (colour (g p))*Y*star (touch (colour (g q))))= touch (colour (g q))*clap Y*star (touch (colour (g p))):=by
    let A:=touch (colour (g p)); let L:=touch (colour (g q)); have hm:star A*J0=J0*star A:=by unfold A; rw [Lat.touch_star]; exact (Lat.interlace ..).eq
    unfold clap; rw [star_mul,star_mul,star_star]; change J0*(L*(star Y*star A))*J0=L*(J0*star Y*J0)*star A; rw [← Matrix.mul_assoc J0, ← flora]; simp only [Matrix.mul_assoc]; rw [hm]
variable {A E:Type}
lemma clapD (W U:Sheet c): foldH (W+U)=foldH W+foldH U:=by unfold foldH; rw [Matrix.conjTranspose_add, Matrix.mul_add,Matrix.add_mul]
noncomputable def flipL : Sheet c →L[ℝ] Sheet c:= LinearMap.toContinuousLinearMap {toFun:= foldH,map_add':=clapD,map_smul':=fun z Z=>by unfold foldH; change _*star _*_=_; rw [star_smul,star_trivial,Matrix.mul_smul,Matrix.smul_mul]; rfl }
lemma soldF (G:Silo c)(η δ M:ℝ)(A:BankP c) (Z:St c)(h:Run.Pack id id η δ B Z M G A)(ht:Torch G) : foldH (Z V)=Z V:=by
    change flipL (Z V)= _; rw [← entriesU h V,map_sum]; have he: Equiv.Perm (Tick c) :=⟨flopT,flopT,fun _=>rfl,fun _=>rfl⟩; let e:Equiv.Perm (Tick c):=⟨flopT,flopT,fun _=>rfl,fun _=>rfl⟩; simp_rw [show ∀ i:Tick c,flipL (pairQ G i V)=pairQ G (e i) V from fun i => (fold_cell G ht i V).symm]; exact Equiv.sum_comp e (fun i=>pairQ G i V)
lemma colorV {B:ℕ}{A':BankP c}(h:Run.Pack id id η δ B U t G A') (hf:0<η)(hu:η≤1)(i:EraM c)(F:Frame c): newDay x i.val G (Lattice.gauge F V)=touch (colour (F (i.val.1)))*newDay x i.val G V*star (touch (colour (F (i.val.2.1+step x)))):=by
    rw [← earnedT,← earnedT]; exact (novaCost x i.val G h i.2 hf hu).2.2.2.2.2 ..
end fold
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.tissue
