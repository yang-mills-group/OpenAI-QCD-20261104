import YM.Massive.Lantern.Width
import YM.VStages.Tokens
import YM.Massive.Lantern.Night
import YM.QCD.Fall.Cool
/-! # actual strengthened crown, for both quoted desk and simultaneous marking input with retained K weights. Exposes unmarked migration relation for any K swap and controlling soft purchases plus distance from unity. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para Metric Set Pine Leaf Tee
variable {t s τ u r d ε α η K W G ν l h b θ v M :ℝ}{j k:ℕ}{B:BudgetPoint}
open Jets.Touch Push Push.AbsoluteSums Footprint WilsonStartup Port AnalyticBridge VerifiedReset Time
open Quotes Collection Averaging Calm
local notation "P⁔"=> Jets.Touch.chip

-- Commitment. exposures leaving Slot.Lights.

variable [Countable I][Countable J][Countable V]
local notation "Jp"=> preExponent
structure VaultRoom (G:Gem c N I)(Y:Ruby.Hue c N J)(F:Rail c N V)(p:BudgetPoint)(U:St c)(W:ℕ→Atom su 2)(T:PathData su)(S:Clip)(b:Flavor N)(m α v' h:ℝ)(L:Side)(x u ν :ℝ)(X: Gem c N (LayerQ c)) (tol:ℝ) : Prop extends ArtifactsR G Y F p U W T S b m α v' h L x u ν X where
    purse : Purchases (Ruby.HJoin Y (Entr.envy G X b T S p α)) p.threshold p.B (v'+1+1) (pra L (betaF su x L)) (speedP L u x)
    near : |powerU G X b-1|≤ tol
    swap :∀ (β:Type) (A:Rail c N β), (∀ i,Summable (Ruby.tK A p.threshold i)) → ∀ (V:Grid c)(B τ:ℝ),wearK c N (powerU G X b) (scoreX G A Y p.threshold (rarity N α τ W T p S B) U V) = scoreV (readyE G X b S T p α) (readyK G A Y X b S T p α) p.threshold (scent W p T S (B+α+betaP G X b) (vac (Reggae.stock (charm G X b)) τ) N) (U+mCoeff G X b • 1) V
    /-- Four-box assertion: permit the next step to be at a smaller stride. -/
    fourP : ForceMass m (roofK L u ν (betaF su x L)) (mCoeff G X b) (4*roofK L u ν x)
    boost : ForceMass m (roofK L u ν (betaF su x L)) (mCoeff G X b) ((L.val:ℝ)/128 *roofK L u ν x)
-- no Φ projection inputs besides Book. solution all stance.
variable {p p' q q':ℝ}(P: RG.Stage)(Q:Plan j)(T:Plan k)
include Q
open Stem
set_option maxHeartbeats 700000 in
lemma crownedBold (u θ Λ:ℝ)(N:ℕ)(hL:0<Λ)(h:0<u)(hf:0<θ)(hU:u+1+1≤ P.supportExponent+1)(hp:4≤j)(hv:4≤k)(hC:P.clip.direct≤1): ∃ F K ν ε :ℝ,0<F∧0<K∧0<ν∧ 0<ε ∧ ∀ (L:Side),512 ≤ L.val → ∀ (v q d A α C tol:ℝ), 0<tol→0<v→ 0<q→ 0< d→0<α→ ∃ M:ℕ, ∀ᶠ x in atTop,
    let t:=betaF su x L; let Z:=P.supportExponent+3; let W:=P.supportExponent+1; let s:= P⁔ L x; let l:=speedP L θ x; let V' := fan L (1/2) t+ payment 1 (4*radiusB t+2) 0 1 1 (flowM L t) W 0
    ∀ (c f:Side)(p:BudgetPoint)(Y:Flight j k)(T':PathData su)(Yp:ℝ)(H:f.val=c.val*Y.L.val),Y.L=L→M*p.B ≤ c.val→Now L p P x→T'.Bounds P.clip P.width P.paths Yp → ∀ (X₁:Garden.Offer 1 d A)(X₂: Garden.Offer 2 α C),
     let U:= wood T 0 Y.land+ blossomT X₁ X₂ (haloK L x) c
     ∃ X:Gem c N (LayerQ c), SlotT X p l (Jp p) F U ∧ ∀ (I J V D:Type)[Countable I][Countable J][Countable V][Fintype D] (G:Gem c N I)(E:Rail c N J)(X':Ruby.Hue c N V)(A: Gem c N D)(P':ℕ→Atom su 2) (b:Flavor N)(μ m:ℝ)(x': Grid c→ EvenA c N)(d:ℝ), |μ|≤ v→ Compass G X' p (ε* P⁔ L t) Z l W V' d x'→ MixedP E → Rail.Reg E p.threshold → (∀ i,Summable (Ruby.tK E p.threshold i)) → Quits E p.B 1 (priceK L q t) (u+1) l → Crossing A → AnchorT A p l Z (Λ*L.val*l^2)→ (∑ i, A.view i 1)= paleF N (Garden.barP Y H * proton Y H) → |m| ≤ roofK L θ ν t →
       let G':=weave G (linen A m); let F':= Ruby.HJoin X' (offT (linen A m) p.threshold)
       Licence p Z (K*s) l G' ∧ Purchases F' p.threshold p.B W (overA L x θ) l ∧ VaultRoom G' F' E p U P' T' P.clip b m μ u F L x θ ν X tol:=by
    let Z:= P.supportExponent+3; let W:= P.supportExponent+1; have ht :0<Z:=by unfold Z; have h:= P.price_pos; linarith
    obtain ⟨K,D,F,hK,hD,hF,hρ⟩:= arrivalR k N P T u θ hf h hU hC; obtain ⟨y,hy,hY⟩:= hauteur N; obtain ⟨ν,ε,r,Yr⟩:= director Λ hK hD hL hF (lt_of_lt_of_le zero_lt_one hy)
    have ha:= Yr.z_p; have he:= Yr.ν_p -- field?
    have hz:= Yr.epsP
    refine ⟨F,K,ν,ε, lt_of_lt_of_le zero_lt_one hF,hK,he,hz,fun L hM v q d A α C tol ht0 hV hQ hh hA=>?_⟩
    obtain ⟨M,hρ⟩:= hρ d α A C hh hA
    obtain ⟨n₀,hm⟩:=level F Z ht (lt_of_lt_of_le zero_lt_one hF) (ε:=r) ha; obtain ⟨n₁,h1⟩:=level (Λ*L.val) Z ht (mul_pos hL (by positivity)) (ε:=r) ha
    obtain ⟨c₀,hc⟩:= eventually_atTop.mp (projecting (N:=N) ha hv hp T Q L F Z ht); obtain ⟨c₁,hL₁⟩:= eventually_atTop.mp (projecting (N:=N) ha hp hv Q T L (Λ*L.val) Z ht)
    refine ⟨M + n₀+n₁+c₀.val+c₁.val,?_⟩
    let z x:= betaF su x L; have hE : Λ*ν>0:=mul_pos hL he
    obtain ⟨Wf,hWf,hf2⟩:=near_money tol ht0
    filter_upwards [((chip_rate L).mul_left (D*K)).below (by norm_num) Wf hWf,hρ L q v hQ hV,pegL L,(Work.E09.betaF_growth su L).eventually (soloCash P L hE N), event_chip L θ, (Work.E09.betaF_growth su L).eventually (event_chip L θ),dim L θ,framesC L θ hf, ((chip_rate L).mul_left (D*K)).below (by norm_num) (1/2) (by norm_num)] with x hWf0 ht₁ hx ht' hZ hZ' hw hR hω
    intro t Z' W' s l V' c f p Y T' Yp H hK' hM' hP he' X₁ X₂ U
    have hB:=p.B_pos; have hE₁ (k:ℕ)(hh:k≤ M +n₀+n₁+c₀.val+c₁.val) : k*p.B ≤ c.val:= (Nat.mul_le_mul_right _ hh).trans hM'; have hd (k:ℕ)(hh:k*p.B ≤ c.val): k ≤ c.val := (Nat.le_mul_of_pos_right k hB).trans hh
    obtain ⟨X,Hs,HK⟩:= ht₁ c p T' X₁ X₂ Y.land Yp (hd M (hE₁ M (by omega))) hP he'
    refine ⟨X,Hs,?_⟩; intro I J V D₀ _ _ _ _ G E X' A P' b μ m x' a' hμ hg heM hy' hℓ hΩ hX hΦ ha' hl G' F'
    let g:=P⁔ L t; let ℓ:=speedP L θ t; have hm':Jp p=Z':=by unfold Quotes.preExponent; rw [hP.era.2.2]
    have hI:= hP.ball; have hℓ':l≤ ℓ:=mul_le_mul_of_nonneg_left hR.2.2.2 (by norm_num); have hh' : 1 ≤ l:=by unfold l speedP; linarith [hR.2.1]
    have hv₀:= hZ.2.1; have hw := mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ) ≤ 2); have hU₂ : ℓ≤ 2*l:=by unfold l ℓ speedP; linarith only [hw]
    have ht':=ht' -- need parameters
    let dM := Λ*(L.val:ℝ)*l^2; have hN:= estim (m:=m) (K:=Λ) (side_pos L) (lt_of_lt_of_le zero_lt_one hh') ((lt_of_lt_of_le zero_lt_one hh').trans_le hℓ') hZ'.2.1 hℓ' hl he hL.le
    have hΞ:= sizeζ A m hΦ; have hW: W'+1+1 ≤ Z':= le_of_eq (by unfold Z' W';ring); have hX':= clock A m hX; have ht₀ : 0 ≤ W':= by have h:=P.price_pos; unfold W'; linarith
    have hΨ:= starsX _ hΞ hX' (lt_of_lt_of_le zero_lt_one hh') ht₀ hW
    have hζ: Licence p Z' (K*s) l G':= wells _ (guardL G _ hg.costE hΞ.law) le_rfl (add_le_add_right hN _|>.trans ?_); swap
    · have hh := (mul_le_mul_of_nonneg_right Yr.Θg hv₀.le); have hz':= hx.2; exact (add_le_add (mul_le_mul_of_nonneg_left hz' hz.le) (mul_le_mul_of_nonneg_left hz' hE.le)).trans (by unfold s; linarith only [hh])
    have hΘ:= joinsM _ _ hg.costY hΨ
    have hνM: Purchases F' p.threshold p.B W' (overA L x θ) l:=by
         refine scant _ hΘ le_rfl ?_; dsimp only [overA]; rw [hP.ball]; exact ht' _ (mul_nonneg (abs_nonneg _) (by positivity)) hN -- same
    have hχ: Purchases F' p.threshold p.B (p.supportExponent+1) (overA L x θ) l:=by rw [hP.era.2.2]; exact hνM
    obtain ⟨hp',hv'',hu,hC',hk',hV'',hTK,hf'⟩:=HK μ hμ _ _ _ G' E F' b (pilot G _ hg.wardG hX') hζ heM hy' hℓ hΩ hχ
    have hMq : |qMass (till X b 0)|≤ r:= (hc c (hd c₀.val (hE₁ _ (by omega))) p (hm p.B hB c (hE₁ _ (by omega))) _ X b _ (lt_of_lt_of_le zero_lt_one hh') Hs.moveG (show Licence p Z' _ l X from hm' ▸ (show Licence p (Jp p) (F*l^2) l X from Hs.warp.law))).1 Y.land (by rw [Hs.trunk]; unfold blossomT; simp only [Pi.add_apply]; rw [Fork.pale _ (by decide),Fork.pale _ (by decide),zero_add,add_zero]) -- syntax
    have hY₀ : |qMass (till A b 0)-(L.val:ℝ)|≤ r:= (hL₁ c (hd c₁.val (hE₁ _ (by omega))) p (h1 p.B hB c (hE₁ _ (by omega))) _ A b _ (lt_of_lt_of_le zero_lt_one hh') hX hΦ.law).2 f Y H hK' ha'
    have hu4 : l^2*|qMass (till G b 0)|≤ ν*s/128:=by
         apply ((hY c I G p Z' _ _ hg.costE (lt_of_lt_of_le zero_lt_one hh') ht.le b).1).trans
         have hh:= mul_le_mul_of_nonneg_right Yr.betaN hv₀.le; have ht':= (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 hz.le) (zero_le_one.trans hy)); exact ht'.trans (by unfold s; linarith only [hh])
    have hx₂ : l^2*|legϑ G' X b| ≤ D*K*s:=hk'.trans_eq (mul_assoc ..).symm
    have hL': 512≤ (L.val:ℝ):=by exact_mod_cast hM
    have hBoth: ForceMass m (roofK L θ ν t) (mCoeff G' X b) (2*roofK L θ ν x)∧ ForceMass m (roofK L θ ν t) (mCoeff G' X b) (4*roofK L θ ν x) ∧ ForceMass m (roofK L θ ν t) (mCoeff G' X b) ((L.val:ℝ)/128 *roofK L θ ν x):=by
        refine adlerTowers b G X A (fun m'=>weave G (linen A m')) rfl hg.costE hΦ hL' (lt_of_lt_of_le zero_lt_one hh') ?_ ?_ ?_ hMq hu4 hx₂ Yr.ξN he hv₀ (legQx _ _ _ ?_) ht.le
        · have he₁: l^2*roofK L θ ν x=ν*s/L.val:=by unfold roofK Emax l; unfold s; have h:0<fan L θ x:=fan_pos ..; unfold speedP; field_simp
          exact he₁.le
        · linarith [abs_le.mp hY₀|>.1,Yr.z_s]
        · unfold roofK; rw [div_mul_cancel₀ _ (side_pos L|>.ne')]
          apply worthA (m:=Emax _ _ _ _) he hU₂ (lt_of_lt_of_le zero_lt_one hh') ((lt_of_lt_of_le zero_lt_one hh').trans_le hℓ') (by change s/2 ≤ g; linarith only [hx.1]) hv₀ rfl
        · apply le_of_mul_le_mul_left ((hx₂.trans ((le_abs_self _).trans hω)).trans ?_) (pow_pos (lt_of_lt_of_le zero_lt_one hh') 2); nlinarith only [one_le_pow₀ hh' (n:=2)]
    refine ⟨hζ,hνM, ⟨Hs,⟨hp',hv''⟩,hu,hV'',hBoth.1,?money, fun V i j=>hf' _ E hℓ V i j (fun U=> -(N* Extra.Iteration.action P' U))⟩,hTK,?near,(fun t v h b vZ τ=>hf' t v h b vZ τ (fun U=> -(N* Extra.Iteration.action P' U))),hBoth.2.1,hBoth.2.2 ⟩
    case near =>
       apply hf2; apply le_of_mul_le_mul_left (a:=l^2) _ (by positivity) -- check parameter
       calc l^2*|legϑ G' X b| ≤ _:=hk'
            _ ≤ D*K*s:=le_of_eq (mul_assoc ..).symm
            _ ≤ Wf:= (le_abs_self _).trans hWf0
            _ ≤ l^2*Wf:=le_mul_of_one_le_left hWf.le (one_le_pow₀ hh')
    case money =>
        unfold mCoeff; rw [abs_mul, abs_sq]; apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp'.le hv'' 2) (abs_nonneg _))
        have hp : l^2*|legA G' X b|≤1/2:= (hC'.trans_eq (mul_assoc ..).symm).trans ((le_abs_self _).trans hω)
        have hz: |legA G' X b|≤1/2:= (le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hh')).trans hp; linarith
end YM.QCD.Finch

#print axioms YM.QCD.Finch.crownedBold
