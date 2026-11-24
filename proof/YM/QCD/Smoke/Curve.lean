import YM.QCD.Smoke.Vary
import YM.Push.LOOP_COEFFICIENT.Color

/-! # scalar principles at the critical germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {f c F : Side} {V: Grid f→Sheet f} {j k:ℕ}
variable (P:Flight j k)(h:f.val=c.val*P.L.val)(T:Plan j)
local notation "ρ"=> sliceL P h
lemma high_vow (hV: Blank V)(U:Grid f)(p: Lat.Frame f) : shiftH P h T V (Lattice.gauge p U)=aura (siteRot p) (shiftH P h T V U):=by
  let K:= siteRot (p ∘ (sliceL P h).embed)
  unfold shiftH vaultF; rw [hV.1,orbital,gauges, aura_add,aura_add]; exact congr_arg₂ (·+·) (congr_arg (fun x:Sheet f=> _+x) (momentum (shiftH P h T V U) _ K _ (siteRot_u _) (siteRot_u _)|>.1.symm)) rfl
lemma high_day (hV:Blank V)(U:Grid f)(b:Site c){d : Site f→ℂ}(hp:Glare 1 0 0 ((sliceL P h).embed b) d):
    shiftH P h T V (pull 1 ((sliceL P h).embed b) U) = aura (hues ((sliceL P h).embed b) 1 d 1) (shiftH P h T V U):=by
  let W: Sheet f:= hues ((sliceL P h).embed b) 1 d 1
  have he : V (pull 1 ((sliceL P h).embed b) U)=aura W (V U):=by
    have ht:= hV.2.2.1 _ d (rubber hp) U; rw [rubber_eq] at ht; unfold aura; rw [← show _=W* _ from ht, Matrix.mul_assoc,show W*star W=1 from (colour_wheel hp Swing.none).2,mul_one] -- check tactic
  unfold shiftH; rw [aura_add]; apply congr_arg₂ (· + ·) _ he
  have hv : (ρ).embed 0=0:=map_zero (ρ).root
  have hh : Glare 1 ((ρ).embed 0) ((ρ).embed 0) ((ρ).embed b) d:=by rw [hv]; exact hp
  have ht:= spin_vault P h hh Swing.none U T; dsimp only at ht; rw [hv] at ht; exact ht
lemma high_drift (hV:Blank V)(U:Grid f)(s:Signed){d : Site f→ℂ}{C:Spike}(hp: Glare s 0 0 (0:Site f) d)(hh:Swing s C):
    shiftH P h T V (pull s 0 U)=aura (hues 0 s d C) (shiftH P h T V U):=by
  unfold shiftH; rw [aura_add, hV.2.1.port _ s d C hp hh]; congr 1
  have he: (ρ).embed 0=0:=map_zero (ρ).root
  have hv: Glare s ((ρ).embed 0) ((ρ).embed 0) ((ρ).embed 0) d:=by rw [he]; exact hp
  have ht:= spin_vault P h hv hh U T; dsimp only at ht; rw [he] at ht; exact ht

variable {P h T}
variable {p:Clip}{C : KernelChoices}{D:PathData su}{E : Forest (Venue P C h).ratio} {μ δ B K Λ : ℝ}
    {u : Bid.Dir su c→AxisChart su E}(ha: Critical E p D u)(he : Bid.Larger (G:=su) (Venue P C h))(hR:D.Bounds p δ B Λ) (hV:Blank V) (w:ℝ)(T:Plan j)
local notation "W₀"=> Venue P C h
local notation "L₀"=> lap ∘ (notch w) ∘ shiftH P h T V

-- negative local log. unshifted entries mixed. no coherence implicit.
def chimney (w:ℝ)(T:Plan j)(E:Forest (Venue P C h).ratio)(V: Grid f→Sheet f) (u : Bid.Dir su c→AxisChart su E)(q:Site c) (x:Cnr c):= heartP ρ (lap (notch w (shiftH P h T V (encamp E u x).1))) q
-- grant scalar covariance
include ha he hR hV
lemma sunset {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] [CompleteSpace X]
    {U: X→ Joint su c f} {b:X→Cnr c} (t:(W₀).Choices)(hp:Thaw U 0)(hm: U 0=1)(hn:b 0=0)(hx:ContDiffAt ℝ ω b 0)(hh:∀ᶠ x in 𝓝 0,Shell W₀ t p D (input su c (b x)) (U x)):
    ∀ᶠ x in 𝓝 0,∀ q, chimney w T E V u q (b x)= heartP ρ ((L₀) (U x).1) q:=by
  let X:= Classical.choice (Push.Uniform.pre_order su δ B P.patch.J C (show 3 ≤ 4 by decide))
  obtain ⟨hQ,hD,-⟩:= X.full_pack (S:=W₀) E t hR he rfl rfl
  filter_upwards [veterans ha he.1 hR hQ hD t hp hm hx hn hh] with x H₀
  intro q; unfold chimney; rw [← H₀, cloak,wages]; dsimp only; rw [high_vow P h T hV, lap_orbit _ _ (siteRot_u _), shineP]; rfl
include ha he hR hV
lemma sun_public {G:Forest (W₀).ratio}{v : Bid.Dir su c→AxisChart su G} (hh:Critical G p D v)(q:Site c): chimney w T G V v q=ᶠ[𝓝 0] chimney w T E V u q:=by
  let t: (W₀).Choices := Classical.arbitrary _
  filter_upwards [sunset (U:=encamp G v) (b:=id) ha he hR hV w T t (camp_thaw hh) (encamp_zero hh) rfl contDiffAt_id (camp_station hh he.1 hR t)] with x Hx
  exact (Hx q).symm
lemma zodiac (b:Site c)(x:Site c) : chimney w T E V u b ∘ (spaceShift x)=ᶠ[𝓝 0] chimney w T E V u (b+x):=by
  obtain ⟨d,Hd⟩:= shades 1 0 0 ((ρ).embed x)
  let hp:=colour_wheel Hd Swing.none; let t:=Classical.arbitrary (W₀).Choices
  let U:=road W₀ x ∘ (encamp E u); have hv : U 0=1:=by unfold U; rw [Function.comp_apply, encamp_zero ha,road1]
  have hs :∀ᶠ z in 𝓝 0, Shell W₀ t p D (input su c (spaceShift x z)) (U z):=by
    filter_upwards [camp_station ha he.1 hR ((W₀).withinChoice 1 x t)] with z H; rw [input_run]; exact updated W₀ x _ _ _ _ _ he.1 H
  filter_upwards [sunset ha he hR hV w T t (road_diff W₀ x (camp_thaw ha)) hv (map_zero _) (spaceShift x).contDiff.contDiffAt hs] with y H'
  rw [Function.comp_apply,H' b]; let q:= (encamp E u y).1
  change heartP ρ (lap (notch w (shiftH P h T V (pull 1 ((ρ).embed x) q)))) b= _ -- syntax
  rw [high_day P _ T hV _ x Hd,lap_orbit _ _ hp, beacon (ρ) 1 x d 1 hp P.patch.odd_side]
  rw [affine,show Signed.act (1:Signed) b=b by simp]; rfl
lemma horizon (x:Site c) (s: Signed): chimney w T E V u x ∘ orderTurn s=ᶠ[𝓝 0] chimney w T E V u (s.act x):=by
  obtain ⟨d,hp⟩:= shades s 0 0 (0:Site f); obtain ⟨l,hl⟩:∃ l, Swing s l := ⟨_,fleetLeft s⟩
  let t:= Classical.arbitrary (W₀).Choices
  let U:= fun y=>twistUniform s (encamp E u y)
  have he': U 0=1:=by unfold U; rw [encamp_zero ha,twistUniform_one]
  have hs:∀ᶠ i in 𝓝 0,Shell W₀ t p D (input su c (orderTurn s i)) (U i):=by
    filter_upwards [camp_station ha he.1 hR ((W₀).withinChoice s 0 t)] with x H; erw [← flip_links s x]; exact sail s t he.1 _ _ H
  filter_upwards [sunset ha he hR hV w T t (stationed_twist s (camp_thaw ha)) he' (map_zero _) (orderTurn s).contDiff.contDiffAt hs] with z hz
  rw [Function.comp_apply,hz x]; let q:= (encamp E u z).1; change heartP ρ (lap (notch w (shiftH P h T V (pull s 0 q)))) x=_
  have he:=colour_wheel hp hl
  rw [high_drift P h T hV q _ hp hl,lap_orbit _ _ he]
  have hv : (ρ).embed 0=0:=map_zero (ρ).root
  have H:= beacon ρ s 0 d l (by rw [hv]; exact he) P.patch.odd_side (lap (notch w (shiftH P h T V q))) x; rw [hv,affine,add_zero] at H; exact H
lemma preserve (x: Site c) :∀ᶠ y:Swatch su c in 𝓝 0,chimney w T E V u x (moveField y)=chimney w T E V u x y.2:=by
  let t:= Classical.arbitrary (W₀).Choices
  let U (z:Swatch su c):= wages W₀ 1 (switchSite z.1) (encamp E u z.2)
  have hx : U 0=1:=by simp only [U,Prod.fst_zero,Prod.snd_zero,switch_zero,wages_zero]; exact encamp_zero ha
  have hp: Thaw U 0:= ((Thaw.comp (x:=(0:Swatch su c)) (g:=encamp E u) (w:=Prod.snd) (camp_thaw ha) contDiffAt_snd)).wages W₀ (Army.park _ _) (Army.powG (v:=Prod.fst) contDiffAt_fst)
  have hy: ∀ᶠ z : Swatch su c in 𝓝 0, Shell W₀ t p D (input su c (moveField z)) (U z):=by
    filter_upwards [moveField_germ (G:=su) (m:=c),(continuous_snd.tendsto (0:Swatch su c)).eventually (camp_station ha he.1 hR t)] with z H hV; rw [H]; exact hV.wage he.1 hR 1 _
  filter_upwards [sunset ha he hR hV w T t hp hx moveField_zero moveField_analytic.contDiffAt hy] with y H
  rw [H]; unfold chimney; rw [show (U y).1=(encamp E u y.2).1 from gauge_one _]; rfl
lemma paletteP (x:Site c)(k:su.El) : chimney w T E V u x ∘ stain k=ᶠ[𝓝 0] chimney w T E V u x:=by
  let Q : Grid f→Sheet c:=fun U=> ((↑(heartP ρ ((L₀) U) x)):ℂ) • 1
  have hh : Rooted W₀ Q:=fun b u=> by unfold Q; simp_rw [Function.comp_apply]; rw [high_vow P h T hV u b,lap_orbit _ _ (siteRot_u _),shineP,aura_scale, aura_one (siteRot_u _)]
  let t:= Classical.arbitrary (W₀).Choices; let X:= Classical.choice (Push.Uniform.pre_order su δ B P.patch.J C (show 3≤4 by decide)); obtain ⟨hp,hk,-⟩:= X.full_pack (S:=W₀) E t hR he rfl rfl
  filter_upwards [Quarry.static ha t he.1 hR hp hk hh k] with y H
  unfold Quarry.mirage Q at H; rw [aura_scale,aura_one (siteRot_u _)] at H
  let i:=Classical.arbitrary (Row c); have ht:= congr_arg (fun Z:Sheet c=> Z i i) H; simp only [Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one, Complex.ofReal_inj] at ht; exact ht
end YM.QCD.Smoke
