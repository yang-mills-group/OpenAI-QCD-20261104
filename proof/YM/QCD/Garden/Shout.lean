import YM.QCD.Garden.Lift

/-! # Linear response of shiftL to extra dust at origin -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch
open Orbit Orbit.Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f L: Side}{K:KernelChoices}{j k m:ℕ}{p:Clip}{D: Flight j k}{A : Plan j}{I:Type}{W:I→Bloom m}{r B:ℝ}
variable {e:f.val=c.val*D.L.val} {M:Grid f→Sheet f}
variable {R:PathData su} {T:Forest (Venue D K e).ratio} {u:Bid.Dir su c→AxisChart su T}{C : Towers (Venue D K e).patch.L}
local notation "J"=>tied D e 0

def barP (D:Flight j k)(e:f.val=c.val*D.L.val):= conn D e * (father D e)⁻¹
section
lemma rotateP (P:Plan j): barP D e=chirality c*(proton D e)ᴴ*chirality f:=by
  let X:=father D e; let Y:=chirality f; let Q:=conn D e; let Z:=chirality c
  change Q*X⁻¹=Z*((X⁻¹*Qᴴ)ᴴ)*Y
  have he : Cost.Chiral (chirality f) (father D e) := by rw [← tree_zero P]; exact ticketStar ..
  have hx : star X=Y*X*Y:=he
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose,show star X⁻¹=(star X)⁻¹ from (Matrix.conjTranspose_nonsing_inv _),hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hy : Y⁻¹=Y:= Matrix.inv_eq_left_inv chi_sq
  have hz : Z*Q=Q*Y:= (tiedSpin D e 0 1 _).symm -- defeq Q
  rw [hy]; simp only [← Matrix.mul_assoc]; rw [hz, Matrix.mul_assoc Q Y Y,show Y*Y=1 from chi_sq, Matrix.mul_one,Matrix.mul_assoc _ Y Y, show Y*Y=1 from chi_sq, Matrix.mul_one]

end

def windows (D:Flight j k)(K:KernelChoices)(e:f.val=c.val*D.L.val)(M:Grid f→Sheet f)(A:Plan j)
    (W:I→Bloom m)(T:Forest (Venue D K e).ratio)(u : Bid.Dir su c→AxisChart su T):=
    mirage T (shiftL D e A (M+dust W f)) u - mirage T (shiftL D e A M) u

lemma by_window (U:Grid f)
    (hp:IsUnit (shiftH D e A M U).det)(he:IsUnit (shiftH D e A (M+dust W f) U).det): shiftL D e A (M+dust W f) U-shiftL D e A M U=
      (J U*(shiftH D e A (M+dust W f) U)⁻¹) *dust W f U*((shiftH D e A M U)⁻¹*(J U)ᴴ):=by
  let Q:=tied D e 0 U; let S:=shiftH D e A (M+dust W f) U; let E:= shiftH D e A M U
  have hE : dust W f U=S-E:=by dsimp only [S,E,shiftH, Pi.add_apply]; abel
  change (1-Q*S⁻¹*Qᴴ)-(1-Q*E⁻¹*Qᴴ)=Q*S⁻¹*dust W f U*(E⁻¹*Qᴴ)
  rw [hE,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc Q S⁻¹ S, Matrix.nonsing_inv_mul S he,Matrix.mul_one,Matrix.mul_assoc _ E,← Matrix.mul_assoc E,Matrix.mul_nonsing_inv E hp,Matrix.one_mul,← Matrix.mul_assoc Q E⁻¹]; abel

lemma raid {X:Type}{a b c: Side}{A: X→Rail a b}{B:X→Rail b c}{p:Filter X}{M:Rail a b}{N:Rail b c}(h:Tendsto A p (𝓝 M))(he:Tendsto B p (𝓝 N)) : Tendsto (fun x=> A x*B x) p (𝓝 (M*N)):= (show Continuous (fun i:Rail a b×Rail b c=> i.1*i.2) by fun_prop).continuousAt.tendsto.comp (h.prodMk_nhds he)
lemma per_window (hu : Critical T p R u)(hv: Blank M)(ha : Blank (M+dust W f))(he :Guessed (S:=Venue D K e) T (installed (Venue D K e).ratio C.A0) u) (hr:0<r)(h: Fractal W r B)(x:Cnr c):
    Tendsto (fun t:ℝ=> (t^m)⁻¹ • windows D K e M A W T u (t • x)) cutRay (𝓝 ((barP D e)*(∑' i,epilogue (W i) (rise T C x))*proton D e)):=by
  let U (y:Cnr c):= (encamp T u y).1
  have h0 : U 0=1:=by unfold U; rw [encamp_zero hu]; rfl
  have hU : Army U 0 := (camp_thaw hu).1
  have ht {M:Grid f→Sheet f} (hv:Blank M): Tendsto (fun y=> (shiftH D e A M (U y))⁻¹) (𝓝 0) (𝓝 ((father D e)⁻¹)):=by
    have H : ContinuousAt (fun y=> shiftH D e A M (U y)) 0:= (ContinuousAt.add ((canopy ..).continuousAt.comp hU.cont) ((mir_ink_sync hU h0 hv.2.2.2.2).continuousAt))
    apply (continuousAt_matrix_inv (father D e) (by rw [show Ring.inverse=fun x:ℂ=>x⁻¹ from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ (high_rank D e).ne_zero)).tendsto.comp (f:=fun y=>shiftH D e A M (U y))
    simpa only [shiftH,h0,hv.2.2.2.1,add_zero,tree_zero] using H.tendsto
  let E (y):=shiftH D e A M (U y); let S (y):=shiftH D e A (M+dust W f) (U y); let Q(y):=tied D e 0 (U y)
  have hQ : Tendsto Q (𝓝 0) (𝓝 (conn D e)):=by
    have h : ContinuousAt Q 0:= (tied_cont ..).continuousAt.comp hU.cont; rw [← show Q 0=conn D e by unfold Q; rw [h0]]; exact h.tendsto
  have hL: Tendsto (fun y=> Q y*(S y)⁻¹) (𝓝 0) (𝓝 (barP D e)) := raid hQ (ht ha)
  have hF: Tendsto (fun y=> (E y)⁻¹*(Q y)ᴴ) (𝓝 0) (𝓝 (proton D e)):= raid (ht hv) ((show Continuous (fun B:Rail c f=> Bᴴ) by fun_prop).continuousAt.tendsto.comp hQ)
  refine (raid (raid (hL.comp (along x)) (germ hu he hr h x)) (hF.comp (along x))).congr' ?_
  filter_upwards [(along x).eventually (neighbo D A e hv hU h0),(along x).eventually (neighbo D A e ha hU h0)] with t ht hb
  change Q (t • x)*(S (t • x))⁻¹*((t^m)⁻¹ • dust W f (U (t • x))) * ((E (t • x))⁻¹ * (Q (t • x))ᴴ)=(t^m)⁻¹ • (shiftL D e A _ (U (t • x))-shiftL D e A _ (U (t • x)))
  rw [Matrix.mul_smul, Matrix.smul_mul, by_window _ ht hb]
end YM.QCD.Garden
