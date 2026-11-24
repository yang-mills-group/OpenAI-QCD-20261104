import YM.Clink.Gust
import YM.Clink.Storm
/-! Cart paid. Projection at authentic Birth.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays TableT
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
open Next.Free QCD.Entr QCD.Entr.Meridian QCD.Flume
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)(W:QCD.Flume.Plan d)(H:Train d)(z:ℝ)
local notation "φ"=> A.density i
local notation "G"=> corm (i:=i) A d W H z a
local notation "Y"=> report A (G 0) u i 0
local notation "P"=> rayC φ a
open QCD.Entr.Goals Patria.Gall.Seals
local notation "S₀"=> cedar d W H z M (1:Grid M)
local notation "D"=>P - S₀
local notation "V"=> foil φ Y
local notation "Q"=> shift 0 (1:Grid c) s
local notation "O"=> punct (0:Site c)
local notation "U'"=>Stew.delta (1:Grid c) s
lemma flay(X:Sheet c)(hx:Globe.Beam X 1 C): ‖Cahoots.viewX T t (((U'*O)*X)-X*(O*U'))‖ ≤8*C:=by
       let f (A:Sheet c):= (A*O)*X-X*(O*A); let Vx:=viewX (c:=c) T t; let U₁:=fun x:Site c=>touch (thread (0:Site c) (1:Grid c) s x); let e:= Lat.forward (n:=c) s; have hu: Q= rides e U₁:=rfl
       have he(i): separation i (e i)≤1:=Work.E01.sep_step_le i s
       have hp:‖Vx (f Q)‖ ≤8*C:= Cahoots.raysK X t T e U₁ ((surgeP s).1) he hx
       have h:‖Vx (f (star Q))‖ ≤ 8*C:=by
                let Lx:= fun i:Site c=> star (U₁ (e.symm i)); have ht: star Q= rides e.symm Lx:=by rw[hu,Lat.ride_ad]
                rw[ht]; apply raysK X t T _ _ (ht ▸ (surgeP s).1.inP) (fun i=>by rw[separation_comm]; simpa using he (e.symm i)) hx
       change ‖Vx (f (U'))‖ ≤ _; let v:= (2:ℂ)⁻¹; have he: f (U')= v • (f Q-f (star Q)):=by unfold Stew.delta f; simp only [Matrix.smul_mul, Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_sub]; unfold v; rw [← smul_sub]; apply congr_arg; abel
       rw[he,map_smul,norm_smul,map_sub]; refine (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hp h)) (norm_nonneg _)).trans_eq ?_; unfold v; norm_num; ring
include hA hi
lemma saleQ (x:RawVec 10)(hx:Tally T 0 (x.val 0) φ Y)(h:Globe.Beam (P - S₀) 1 C) : ‖wave (qv b (0:Multi 10) (leadR t) x)‖≤8*C:=by
        have hm: chipK 0 (leadR t) b (x.val 0)= Cahoots.viewX T t (Oren.discs b (foil φ Y 1)):=by
             rw[← cluster T (⇑Y) φ b (x.val 0) hx _ _ (by rw[gradeV,gradeL]; norm_num)]; rfl
        rw [←coinedP,hm,scoreW A hA hi a b 0 u W H z hx.unit.self_of_nhds]; split
        next hp=>exact flay (c:=M) 0 t T (P-S₀) h
        next hp=> have hC :0 ≤ C:= (norm_nonneg _).trans (QCD.Globe.Cent.bike h.toR 0 0); rw [map_zero,norm_zero]; positivity
lemma pinch (x:RawVec 10)(hx:Tally T 0 (x.val 0) φ Y)(h:Globe.Beam (P - S₀) 1 C): ‖axM 1 x‖ ≤8*C∧ ‖axM 0 x‖≤ 16*C:=by
       obtain ⟨⟨f,v⟩,rfl⟩:=certified.2 x; let Yx:=plaza (f,v); have ht(b:Flavor 6): ‖f b 1‖ ≤ 8*C ∧ ‖f b 0+f b 1‖ ≤8*C:=by
               let Z(i:Axis):= qv b (0:Multi 10) (leadR i) Yx; have he(i:Axis):‖wave (Z i)‖≤8*C:= saleQ A hA hi a b i u T W H z Yx hx h; have hu : Z 1=f b 1 • (gamma 0*gamma 1):= (life_v ..).2.1; have hh : Z 0=f b 0 • (1:Spike) + f b 1 • (1:Spike) :=(life_v ..).1
               constructor
               · have he:= he 1; rw [hu,waveP,norm_smul,show ‖wave (gamma 0*gamma 1)‖=1 from primeU _ (W_unit _ (Submonoid.mul_mem _ ⟨by simp,by simp⟩ ⟨by simp,by simp⟩)),mul_one] at he; exact he
               have he:= he 0; rw [hh,←add_smul,waveP,wave_one,norm_smul,norm_one,mul_one] at he; exact he
       have hh:0≤ C:= (norm_nonneg _).trans (QCD.Globe.Cent.bike h.toR 0 0)
       constructor
       · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b=>?_ ; change ‖(bodyS _).1 b 1‖≤_; rw[bodyι]; exact (ht b).1
       refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b=>?_ ; change ‖(bodyS _).1 b 0‖ ≤ _; rw[bodyι]; let k:=f b; change ‖f b 0‖≤_; rw [show f b 0=k 0+k 1-k 1 from (by abel : k 0=_)]; apply (norm_sub_le ..).trans; exact (add_le_add (ht b).2 (ht b).1).trans_eq (by ring)
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.pinch
