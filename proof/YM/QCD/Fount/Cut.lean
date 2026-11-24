import YM.QCD.Fount.Vale
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth
variable {t a u r w b m R y p D Y C z κ d s H A δ M θ:ℝ}{L:Side}{g f h B:ℝ→ℝ}
variable {J k N l j:ℕ}
variable {c C':Side}{F:Flight J j}{e:C'.val=c.val*F.L.val}
local notation "G"=> coneK L a
variable {v d W:ℝ→ℝ}
lemma ron (ht:0<a)(hh:Rate su L (-1) v)(hb:Bolt su L g)(hp:Seat L p h)(he:Rate su L 0 f)(hm:Rate su L 0 d)(Z X R D:ℝ)(l N:ℕ): Rate su L (-1+1/16*l) (fun t=> rose Z (G t) D (d t) (g t) X R (v t) (h t) (f t) l N):=by
    let y x:=clump l ((massQ+massQ)*(1+fabric su l Z)^l) (letterP (G x) l*(2*(v x*R))); let S₀:ℝ:= -1+1/16*l; have hy : Rate su L S₀ y:=((((noteJ ht l).mul (((hh.mul_right R).mul_left _))).weaken (by unfold S₀; linarith)).mul_left (l.factorial:ℝ)).mul_right _
    have hv: Rate su L S₀ (fun i=> noteC (G i) (v i*(R*R)) Z l):=((((noteJ ht l).mul (hh.mul_right _)).weaken (by unfold S₀; linarith)).mul_left _).mul_right _
    have hf:= Brim.bell (Brim.prep hp.ruled 2) (Brim.prep he 2); have hx:= (((hb.uses.mul_right (Fintype.card Lat.Fiber)).mul hy).weaken (by rw [zero_add] : 0+ S₀ ≤ S₀)); unfold rose; apply Rate.add (pace S₀ ((hx.mul_left _).add ((hf.mul hv).weaken (by linarith))) (((Rate.const _).add hm).add ((Rate.const _).add hm)) l); exact ((hh.mul (hf.mul_right _)).weaken (by unfold S₀; push_cast; have hh':0≤(l:ℝ):= (by positivity); linarith))
lemma mintBits (Y:ℝ→ℕ→ℝ)(h:∀ i:ℕ,Rate su L (-1+1/16*i) (fun t=> Y t i))(k:ℕ) :∀ᶠ t in atTop,∀ i:ℕ, i ≤ k → 0 < i → Y t i *eaves su L t^i≤ lull L t:=by
    have hh(i:Fin (k+1)):∀ᶠ t in atTop, 0 < i.val → Y t i * eaves su L t ^i.val ≤lull L t:=by
       by_cases hp:0 < i.val
       · have hv:1≤(i.val:ℝ):=by exact_mod_cast hp
         have hc:= ((h i).mul ((edge su L).pow i.val)) (-(35/32):ℝ) (by unfold vow; linarith); exact hc.mono fun i hi _=> (le_abs_self _).trans hi
       exact Eventually.of_forall fun i hi=> (hp hi).elim
    filter_upwards [eventually_all.mpr hh] with x hx i hi hg using hx ⟨i,by omega⟩ hg
lemma leeway (hp:Rate su L (-1) v)(hh:0<C):∀ᶠ x in atTop, v x*C ≤ 1/2 :=by
    filter_upwards [(hp.mul_right C).below (by norm_num) _ (by norm_num : (0:ℝ)<1/2)] with x hx using (le_abs_self _).trans hx
lemma parka {Q: ParcelR}(P:Plan J)(D:ℝ)(S:Patch)(hp:Bolt su S.L g)(hh:0<κ)(ha:0<θ)(hv:Rate su S.L (-1) v)(hy: Rate su S.L 0 d)(ht:Rates Q t)(he:0<δ)(hr:0≤D)(hk:1≤k)(B j':ℕ)(N:ℕ): ∀ᶠ x in atTop, ∀ (c f:Side)(F:Flight J j')(e:f.val=c.val*F.L.val)(T:StepData c f)(I:Forest T.ratio)(U:Tube su T), Quilt U I (g x)→ F.L=S.L→ ∀(X:SunR Q)(V:Grid c→ Sheet c), Own c δ 0 B V D → V 1=Garden.barP F e*proton F e → ∀ ρ:Bid.Dir su c→ AxisChart su I,ρ 0=0 → (∀ y, ‖y‖<eaves su S.L x→Brush k (d x) 1 (Lapis.orbit I ρ) y)→ ∀ m:ℝ,|m| ≤ v x → ∀ y, ‖y‖< eaves su S.L x → let W:=park F e P X.X X.Y (haloK S.L x) 0; Brush k (lull S.L x+lull S.L x) (eaves su S.L x)⁻¹ (amber m (highW S.L κ θ x) W V F e N X.Z.page ρ) y :=by
    let L:=S.L; let Z x:= highW L κ θ x; have hz:Seat L θ Z:= Seat.timesL Seat.keeps _
    obtain ⟨c,hc,hπ⟩:= highGeom N; let f x:= c*g x
    have hf: Rate su L 0 f:=hp.uses.mul_left _; let ψ:=QCD.Smoke.expPrice 2 Q.t*Q.e
    obtain ⟨ν,C',Fq,Y,A,u,i,i',hν,h,hZ,hA,H⟩:=revenueT (k:=j') ht.hr ht.hs P 0 Q.c ψ Q.d Q.t N L ht.ht
    choose z hh' using paint_supply su
    let W' x l:= rose (z l) (coneK L ν x) δ (d x) (g x) D Fq (v x) (Z x) (f x) l N
    have hW (l:ℕ): Rate su L (-1+1/16*l) (fun t=>W' t l):= ron hν hv hp hz hf hy _ _ _ _ _ _
    have h₁:= mintBits W' hW k
    have hu:= (Brim.bell (Brim.prep hz.ruled 2) (Brim.prep hf 2)).mul ((hv.pow 2).mul_right (Fq*Fq*Fq))
    filter_upwards [h₁,kentucky L h,(edge su S.L).below vow_ok 1 zero_lt_one,(hy.mul (edge su S.L)).below (by rw [zero_add]; exact vow_ok) 1 zero_lt_one,hu (- (35/32)) (by push_cast; linarith),hv.below (by norm_num) _ h,(hv.mul_right Fq).below (by norm_num) _ (by norm_num : (0:ℝ)<1/2)] with x hx hK hV hM hu hp ht' c f' F e T I U hT hF X V hR hQ ρ hρ he m hH y hY W
    have ht': v x*Fq ≤1/2:= (le_abs_self _).trans ht'; have hp:= hH.trans ((le_abs_self _).trans hp)
    have hθ: 0<eaves su L x := (norm_nonneg _).trans_lt hY; have hδ: 0≤ lull L x:= (abs_nonneg _).trans hu; let Z':=amber m (Z x) W V F e N X.Z.page ρ
    have hs:(Fintype.card (Modes c N):ℝ) ≤ f x:= (hπ c).trans_le (mul_le_mul_of_nonneg_left hT.primary hc)
    have hg m (hm:|m| ≤ u):= (H X.X X.Y X.Z.page (X.Z.cost ht.ht) (X.Z.permit ht.ht).2 c f' F e m (haloK L x) hF hK.1 hK.2.1 hm).1; have hp':= hg 0 (by simpa using h.le); have hi := he
    have hv: Species F e C' Fq (coneK L ν x) 0 Y i (houseK m W):=(heft ..) ▸ hg m hp; have hb':0<coneK L ν x:=mul_pos hν (pow_pos hK.1 _); have hz:0 < Z x:= mul_pos hh (fan_pos ..); have hB y (hy:‖y‖<eaves su L x) j (hj: j ≤ k)(hh: 1 ≤ j) : ContDiffAt ℝ j Z' y ∧ normJ j Z' y≤ W' x j:= offerK hp' hv hR hr ‹0<δ› hb' hH ht' hz _ _ hh (hh' j) (fun y hg=> (hi y hg).smaller hj) hρ ((le_abs_self _).trans hV) ((le_abs_self _).trans hM) hy hT.finalP hs
    have hZ:= projects hp' hv hb' (hQ.trans (pale (e:=e) (P:=P) X.X X.Y (haloK L x)).symm) hρ X.Z.page N hz hH hs
    have he':= pond hθ (f:=Z') hk hδ hδ (fun i hi=>(hB _ (mem_ball_zero_iff.mp hi) k le_rfl hk).1) (fun i hi he y hz=> (mul_le_mul_of_nonneg_right (hB _ (mem_ball_zero_iff.mp hz) i he hi).2 (by positivity)).trans (hx _ he hi)) (fun i hi=> ?_) y (mem_ball_zero_iff.mpr hY)
    swap
    · obtain rfl:= Nat.lt_one_iff.mp hi; rw [normJ,norm_iteratedFDeriv_zero,pow_zero,mul_one]; exact hZ.trans ((le_abs_self _).trans hu)
    simpa only [Nat.cast_one,one_mul] using he'
end YM.QCD.Fount
