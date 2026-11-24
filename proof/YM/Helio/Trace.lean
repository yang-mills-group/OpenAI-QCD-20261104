import YM.Helio.Sun
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
variable (V:Grid c)(α:Axis)(x:Site c)(d:Tick c)
local notation "Mα"=>wheelS (rplus c α)
def letterP (V:Grid c)(α:Axis)(x:Site c):Bundle:= touch (thread 0 V α x)
lemma risesT : Mα d=(d.1+step α, d.2.1+step α,d.2.2.image (fun i=>i+step α)):=by
   rw [trill,riseA,riseA,(show ⇑(act (rplus c α))= _ from funext (riseA α (c:=c)))]
variable (G:Silo c)
-- [S,D]. one positive. includes translated direction.
noncomputable def newDay (V:Grid c) :Bundle := letterP V α d.1 * fareP G (Mα d) V-fareP G d V *letterP V α d.2.1
lemma basisE (hx:Run.Pack id id η δ B U q G A)(h:Torch G) : fareP G d (overlayP α V)*letterP V α d.2.1=letterP V α d.1*fareP G (Mα d) V:=by
   let o:=d.1; let i:=d.2.1; let F(y:Site c):= V (y,α); let T y:=touch (colour (F y)); let s:= rplus c α; let H:= fun u:Site c=> Lat.seam 0 u α; let W:= lightP s 1 H
   have hk (i:Site c):T i*W i=letterP V α i:=by
       unfold W lightP T F letterP thread H; have hV:= Lat.seam_cases 0 i α; rw [star_one, Lat.wave_one,Matrix.mul_smul,mul_one]; rcases hV with he|he <;> rw [he] <;> simp [Lat.touch] <;> ext <;> simp
   have hℤ : star (letterP V α i)*(letterP V α i)=1:=(touch_u (Lat.thread_u ..)).1
   unfold overlayP; rw [proofC hx, motion G h s H 1 (warrantL α c)]; let m:= fareP G (Mα d) V; change T o*(W o*m*star (W i))*star (T i)*_=letterP V α o*m; rw [← hk o, mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star (W i)), ← star_mul, hk i,hℤ,mul_one,mul_assoc];
lemma rightT (V : Grid c)(a:Axis)(A:Sheet c)(i j:Site c): Run.cell (A*Lat.shift 0 V a) i j = Run.cell A i (j-step a)* letterP V a (j-step a):=by
   nth_rw 1 [← star_star (Lat.shift 0 V a)]; rw [Lat.shift,ride_ad,cell_ride_right,star_star,Lat.back]; rfl
lemma penny (hx:Run.Pack id id η δ B U q G A) (h:Torch G): newDay α d G V=(fareP G d (overlayP α V)-fareP G d V)*letterP V α d.2.1:= by unfold newDay; rw [sub_mul,basisE V α d G hx h]
lemma allot : Lat.shift 0 V α*pairQ G (Mα d) V- pairQ G d V *Lat.shift 0 V α= Stew.block d.1 (d.2.1+step α) (newDay α d G V):=by
   apply Sway.whist; intro i j; rw [show ∀ A B:Sheet c,Run.cell (A-B) i j=Run.cell A i j-Run.cell B i j from fun _ _=>rfl,rightT,Lat.shift,cell_ride_left]; unfold pairQ; rw [pairBl,pairBl,pairBl]; have he := risesT α d
   simp only [hop,he,add_left_inj, sub_eq_iff_eq_add]; split
   next ht=> obtain ⟨ha,hb⟩:=ht; subst i j; simp [newDay,he]; rfl -- pushes he
   next ht=> simp [ht]
lemma ray (hx:Run.Pack id id η δ B U q G A): ∑ i:Tick c,Stew.block i.1 (i.2.1+step α) (newDay α i G V)=Lat.shift 0 V α*U V-U V*Lat.shift 0 V α:=by
   simp_rw [← allot]; rw [← entriesU hx, sum_sub_distrib,← Matrix.mul_sum,← Matrix.sum_mul, Equiv.sum_comp Mα (fun x=> pairQ G x V)]
end Meridian
end YM.QCD.Entr
