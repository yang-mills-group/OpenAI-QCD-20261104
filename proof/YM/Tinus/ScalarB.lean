import YM.Tinus.SumsR
import YM.Tinus.SpectralB
import YM.Tinus.RollerB
import YM.Pods.Typing
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A:Type*}[Fintype A] {c f:Side}{j k F:ℕ}
open Finset
open Patria Patria.Depth Patria.Rolls
variable {S:Scheme} {i m n:ℕ} {R:Side} (A:Run S n R 6) (X:Spike)(x y:Flavor 6)(q:Bool)
local notation "Y"=> film X x y A q m
local notation "W"=> S.side R
variable (t: Massive.Patria.Rolls.Sail)
local notation "G"=> stalk X A x y q m
local notation "Hm"=> ratioTo S m i
set_option maxHeartbeats 420000
lemma horn_scale (v w:ℂ)(F':Lat.Fields c 6) : horn X x y v (w • F')=w * horn X x y v F':=by
    have hp: traceP (w • F')=w • traceP F':=by ext u v; simp [traceP]
    unfold horn; rw [hp,show piece x y (w • traceP F')= w • piece x y (traceP F') from rfl]; unfold spinTest; simp_rw [show ∀ i j:Site c,QCD.Run.cell (w • piece x y (traceP F')) i j= w • QCD.Run.cell (piece x y (traceP F')) i j from fun _ _=>rfl, Matrix.smul_mul,Matrix.trace_smul]; -- ring sum
    simp_rw [← mul_div_assoc,mul_sum]; congr 2; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; change _*(w*_)*_= w*(_* _ * _); ring
variable (X' :Spike)(h:i ≤ m)(hA:A.Actual)(hl:m ≤ n)
set_option quotPrecheck false
local notation "ΔY"=> report A G (.some t) i
local notation "Ω"=> ((↑(ratioTo S m i):ℝ)^4)
include h hA hl
lemma momentumR : PCAC.chord X' x y A i (S.toStop R A.β A.w m i Y)=((Ω:ℝ):ℂ)*(Fintype.card (Site (W i)))*(PCAC.chord X' x y A i (ΔY 0)):=by
       let P:= ΔY; let f : Insertion (W i) 6→ₗ[ℂ]ℂ:={toFun:= PCAC.chord X' x y A i,map_add':= fun i j=> PCAC.chord_add ..,map_smul':=fun v u=> show _ = v * _ from horn_scale ..}; have hh :∀ s:Cover, f (P s)= f (P 0):=by
            intro s; unfold f; change horn X' x y _ _= _; have hp:= stagger X A (.some t) hA x y q hl; have hz:Patria.march s (P 0)=⇑(P s):=by simpa only [P,zero_add] using (hp.moves _ h).trans s 0
            rw [← show _= (P s) 1 from congr_fun hz 1]; exact warmUp ..
       let u:= S.toStop R A.β A.w m i (film X x y A q m); have hf:= congr_arg f (whole_ax A X x y q t h); rw [map_sum] at hf; simp_rw [show ∀ j:Site (W i), f (Depth.report A (stalk X A x y q m) (.some t) i (lift j))= f (P 0) from fun j=> hh _,sum_const] at hf -- bind fun s
       have hp: Ω≠0:=ne_of_gt (pow_pos (Nat.cast_pos.mpr (odd_to h).pos) 4); change _=f ((Ω)⁻¹ • u) at hf; rw [show f ((Ω)⁻¹ • u)= _ from map_smul (f.restrictScalars ℝ) _ u] at hf
       change _= Ω⁻¹ • f u at hf; symm; calc
           _= (↑Ω:ℂ) * (Fintype.card (Site (W i)) • f (P 0)):=by push_cast; rw [mul_assoc,nsmul_eq_mul]; rfl
           _= f u:=by rw [← Finset.card_univ, hf]; change Ω • (Ω⁻¹ • f u)=f u; rw [smul_inv_smul₀ hp]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.momentumR
