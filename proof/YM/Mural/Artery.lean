import YM.Mural.Beet
import YM.Mural.Vitex
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k i m n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable  (Y:Stitch.Tablet P₀ Unit)(A:Unit→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N Unit
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark Unit (VarnC H U N)
local notation "X'" => loommark Unit (sailP H Γ N)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "Β" => Ribbon.banknote N ((S').ratio.parent ∘ A) φ
local notation "Unit'"=> Ribbon.Spine Unit
local notation "mx"=> Keys c N ⊕ Ribbon.Spine Unit
namespace Grove
open PhysicalNext.Repeat.Greenbelt Territory Horticulture
open scoped PhysicalNext.Repeat.Greenbelt
variable {q₁:Unit→Bool}{χ:Chi}{θ a₁ d₁ c₁:ℝ}
variable (hw:Y.Flora O.threshold q₁ A)
set_option linter.unusedSectionVars false

local notation "W!"=> room L' d K H G U Γ Y
local notation "d!"=> (X 1).det^N
variable {χ:Chi}{θ₂ Q₁:ℝ}
variable (h': Pack id id θ₂ a₁ n (wood P' 0 L'.land) q Γ D')
variable (F:Tree.Forest (Flight.visit L' K d).ratio) (hStaid:∀ x,Y.Staid O.threshold x)(hB:0 < radiusB τ)
open Plate PaletteT Cupola Reggae NormedSpace
variable (Θ:Grid f→Grid c→ℂ)(δi: Varn f c)
local notation "eᴬ"=> issuedA L' d K H U A φ Θ δi -- N maybe implicit
local notation "cA"=> mantel L' d K H G U Γ Y A φ eᴬ
variable (hz:∀ V Z,(VarnC H U N).works δi V Z=0) (hp:0<δ)
open Plate PaletteT QCD.Mural Glow
local notation "loc"=> ( (L'.visit K d).ratio.parent∘ A)
local notation "Xg"=> VarnC H U N
local notation "kz"=> Fleet.align U' (issuedA (N:=N) L' d K H U A φ Θ δi)
local notation "vI"=> (Varn f c)
local notation "zT"=> Patio mx
local notation "ζ"=> hinge c N
lemma holi (N:ℕ)(c:Side): Polite qT {()} (hinge c N):= ⟨1, show stake (Keys c N) (Ribbon.burst qT {()}) 1=_ from (by rw [fullB]; rfl)⟩
variable {Z:ℝ} {hu:ℝ} {Ht : Set (Site c)}
local notation "ξw"=> ((Xg).window δi)
local notation "F!"=> ((Xg).fine δi)
variable (H₀:∀ X:Grid f, LocalOn ((VarnC H U N).window δi) (Θ X)) (Hf:∀ V,LocalOn ((VarnC H U N).fine δi) (fun X=>Θ X V))(H₁:Continuous (fun x:Grid f×Grid c=> Θ x.1 x.2))(H₂:∀ i:Lat.Frame f,(∀ j,i ((L'.visit K d).ratio.embed j)=1)→∀ X₁ V',Θ (gauge i X₁) V'=Θ X₁ V')
variable (H₃: (loommark Unit (VarnC H U N)).Famous)(H₄: (loommark Unit (VarnC H U N)).speaking)
lemma plots_me (i₁:vI)(h:i₁≠δi): (issuedA (N:=N) L' d K H U A φ Θ δi i₁)= (U').works i₁:= funext fun _=> funext fun _=>if_neg h
include H₀ Hf H₁ H₂ H₃ H₄
lemma angelic : (kz).Famous∧(kz).speaking:=by
    let g:= Β; let p(x:Grid f× Grid c):= g (Θ x.1 x.2 • ζ); have ht: Continuous p:= g.toLinearMap.toContinuousLinearMap.continuous.comp (show Continuous _ from H₁.smul continuous_const) -- verify
    let X:=kz; have hp U'₁ V:X.works δi U'₁ V=p (U'₁,V):=if_pos rfl; have hh(i:vI)(hi:i≠δi): X.works i=(U').works i:= plots_me L' d K H U A φ Θ δi i hi
    refine ⟨⟨H₃.horizons,H₃.boot,?_,?_,?_,?_,H₃.signs,H₃.issued⟩,fun i=>?_⟩
    · intro i V; by_cases he:i=δi; swap; · change LocalOn (X.fine i) (fun U=>X.works i U V); rw [hh i he]; exact H₃.locally i V
      subst i; intro U V' h; change X.works δi U V=X.works δi V' V; rw [hp,hp]; exact congr_arg (fun z:ℂ=>g (z • ζ)) (Hf V U V' h)
    · intro i V; by_cases he:i=δi; swap; · change LocalOn (X.window i) (X.works i V); rw [hh i he]; exact H₃.read i V
      subst i; intro W U'₁ h; change X.works δi V W=X.works δi V U'₁; rw [hp,hp]; exact congr_arg (fun z:ℂ=> g (z • ζ)) (H₀ V _ _ h)
    · intro i V; change Envelope (fun U=> X.works i U V); by_cases he:i=δi; swap; · rw [hh i he]; exact H₃.pays ..
      subst i; simp_rw [hp]; have hh:Continuous fun U=>p (U,V):=ht.comp (continuous_id.prodMk continuous_const); obtain ⟨j,hj,h⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty hh.norm.continuousOn; exact ⟨hh.measurable, _, fun j=> h (Set.mem_univ j)⟩
    · intro i V Z h PQ; by_cases he:i=δi; swap; · change X.works i _ _ = X.works i _ _; rw [hh i he]; exact H₃.roots i V Z h PQ
      subst i; change X.works δi _ _ = X.works δi _ _; rw [hp,hp]; exact congr_arg (fun z:ℂ=>g (z • ζ)) (H₂ Z h PQ V)
    by_cases he:i=δi; swap; · change Measurable fun x: Grid f × Grid c=> X.works i x.1 x.2; rw [hh i he]; exact H₄ i
    subst i; change Measurable fun x:Grid f × Grid c=> X.works δi x.1 x.2; simp_rw [hp]; exact ht.measurable
omit H₀ Hf H₁ H₂ H₃ H₄
variable (hs:(loommark Unit (VarnC H U N)).gator)(hφ:0<φ)
lemma tile_k (i₁:Varn f c) : siteH i₁ (S').ratio∈(Xg).ground i₁:= halo_subset _ _ (Loom.marks i₁ (S').ratio (radiusB τ) (halo_subset _ _ (mem_singleton_self _)))
lemma signage : (kz).Feasible:=⟨fun i _ _ _=>⟨_,tile_k (N:=N) L' d K H U i⟩⟩
-- seat membership: p().at chosen orbit.
variable (hA: ( (L'.visit K d).ratio.parent ∘ A) () ∈ (VarnC H U N).ground δi)
include hA hs
lemma enough : (kz).gator :=by
    let Y:= kz; intro j V W; by_cases h:j=δi; swap; · change Gated _ (issuedA ..); rw [plots_me L' d K H U A φ Θ δi _ h]; exact hs ..
    subst j; rw [show (kz).works δi V W=Β (Θ V W • ζ) from if_pos rfl]; unfold Gated; rw [map_smul,map_smul]; apply Subalgebra.smul_mem; exact Ribbon.entitled N loc φ _ sD 1 (Subalgebra.one_mem _) fun i _=> by rw [show i.1.1=() from Subsingleton.elim ..]; exact hA -- projection syntax
omit hA hs
noncomputable def medalT (j':Varn f c): Finset Unit:= if j'=δi then {()} else ∅
include hz hφ
lemma lawP (i₁: vI)(U₁:Grid f)(V:Grid c): Mint N loc φ qT (medalT δi i₁) (eᴬ i₁ U₁ V)∧ vacR Unit' (Keys c N) (withdraw N loc φ (eᴬ i₁ U₁ V))= (Xg).works i₁ U₁ V:=by
    let Γ:= U'; by_cases hx:i₁=δi; swap
    · rw [plots_me L' d K H U A φ Θ δi i₁ hx,medalT,if_neg hx]; let x:= (Xg).works i₁ U₁ V; have hh:(U').works i₁ U₁ V =bearing Unit c N x:=rfl; rw [hh]; refine ⟨PaletteT.kindle N loc φ hφ x, ?_⟩; rw [← braces Unit loc]; exact (congr_arg (vacR Unit' (Keys c N)) (Cupola.home N loc φ hφ _)).trans (off _ x) -- kindle args proof rewrote to banknote! edit
    subst i₁; rw [medalT,if_pos rfl,show eᴬ δi U₁ V= Β (Θ U₁ V • ζ) from if_pos rfl]; have hh:= (holi N c).smooch (Θ U₁ V); refine ⟨Mint.initiate _ hφ _ hh,?_⟩; rw [Cupola.home N loc φ hφ,Twist.bleaching _ _ _ hh (singleton_nonempty _),hz]
omit hz
set_option maxHeartbeats 580000 in
set_option maxRecDepth 3000 in
lemma cashPrint (t:ℝ)(N:ℕ)(i:ℕ)(z:ℂ) (v: Unit→Site c): ‖paidM (family c N Unit) t i φ (banknote N v φ (z • hinge c N))‖= ‖z‖:=by
    let w:= pluck (Keys c N) (Ribbon.burst qT {()}); have hp: w (hinge c N)=1:= by unfold w; rw [fullB]; exact Ribbon.quid ..
    have he: w (z • hinge c N) = z • 1:=by rw [map_smul,hp]
    let x:= z • hinge c N; have hZ: premiumG c N Unit φ t i (banknote N v φ x)= repay (univ:Finset (Keys c N)) t i (fun _=>φ) (w x):=(pennedM c N Unit v φ t i hφ x ((holi N c).smooch z)).trans (attachedM c N Unit φ t i hφ x ((holi N c).smooch z))
    change premiumG _ _ Unit _ _ _ _=‖z‖; rw [hZ,show w x=z • 1 from he,repayL,repay_one,mul_one]
variable (x α:ℝ) (p':Varn f c→ℝ)(y0:ℝ)(h0:0 ≤y0)(J0:Finset (Varn f c))(M₀:ℕ)
variable (hp0:∀ U₁:Grid f,∀ V:Grid c, ‖Θ U₁ V‖≤ Real.exp α*y0)
variable (hX:Vigil (loommark Unit (VarnC H U N)) (family c N Unit) F (fun i=>siteH i (L'.visit K d).ratio) p' x M₀ φ α J0 (18*radiusB τ) (L'.L.val^4+1)) -- binders.local notation
variable (hh:∀ (X: Coat T F),X.x=τ → X.width=o.K → X.manifest →∀ z: Air f su, (VarnC H U N).riseP X z δi≠0 → ¬ Inside (siteH δi (L'.visit K d).ratio) X.seeds (18*radiusB τ) → ‖Θ (X.input (X.liftA β z)) X.V‖ ≤ y0)
include hp0 hX hh h0
lemma heritage : let p(i: Varn f c):= p' i+(if i=δi then y0 else 0); Vigil kz (family c N Unit) F (fun i=> siteH i (S').ratio) p x M₀ φ α (insert δi J0) (18*radiusB τ) (L'.L.val^4+2):=by
    intro p; let Yp:=kz
    let PP:=paidM (family c N Unit) x M₀ φ
    have he(Q₀: Coat T F) z: ‖PP (Yp.coming δi Q₀ z)‖≤ ‖Θ (Q₀.input (Q₀.liftA β z)) Q₀.V‖:=by
       refine (riseFee Yp (family c N Unit) ..).trans (?_) -- riseFee missing args?
       exact Eq.trans_le (congr_arg (fun x=> ‖PP x‖) (show Yp.works δi _ _=_ from if_pos rfl)) (cashPrint φ hφ x N M₀ _ _).le
    have hz(i)(hi:i≠δi)(Q₀:Coat T F)(z): Yp.coming i Q₀ z=(U').coming i Q₀ z:=by change _ • eᴬ i _ _ = _; rw [plots_me L' d K H U A φ Θ δi _ hi]; rfl
    have hP i:p' i ≤ p i:= le_add_of_nonneg_right (ite_nonneg h0 le_rfl)
    have hT:y0 ≤ p δi:=by unfold p; rw [if_pos rfl]; exact le_add_of_nonneg_left (hX.rise _)
    refine ⟨hX.grow,fun i=>(hX.rise i).trans (hP i),?_,fun i Q₀ ht hy hf z hc=>?_,fun i Q₀ ht hy hv z=>?_⟩
    · intro i; let f(j):=siteH j (S').ratio=i; have he: (insert δi J0).filter f⊆insert δi (J0.filter f):=by intro j hj; simp only [mem_filter,mem_insert] at *; tauto
      exact (card_le_card he).trans ((card_insert_le ..).trans (Nat.add_le_add_right (hX.seat i) 1))
    · by_cases h:i=δi; swap; · unfold PP at *; rw [show (kz).coming i Q₀ z= _ from hz i h Q₀ z] at hc; obtain ⟨h1,h2⟩:= hX.rare _ Q₀ ht hy hf z ((hP _).trans_lt hc); exact ⟨mem_insert_of_mem h1,h2⟩
      subst i; have h: Inside (siteH δi (S').ratio) Q₀.seeds (18*radiusB τ):=by
            by_contra hi
            have hx : (VarnC H U N).riseP Q₀ z δi≠0:=by
               intro h; have he: Yp.riseP Q₀ z δi=0:=h; change p δi< ‖PP (Yp.coming ..)‖ at hc; unfold coming at hc; rw [he,zero_smul,map_zero,norm_zero] at hc; exact not_lt_of_ge ((hX.rise _).trans (hP _)) hc
            exact not_lt_of_ge (((he Q₀ z).trans (hh Q₀ ht hy hf z hx hi)).trans hT) hc
      obtain ⟨j,hj,h⟩:= halo_spec.mp h; exact ⟨mem_insert_self ..,j,halo_spec.mpr ⟨siteH δi (S').ratio,marks δi _ _ (halo_subset _ _ (mem_singleton_self _)),(separation_comm ..).trans_le (h.trans (show 18*B ≤30*B from by omega))⟩,hj,h⟩
    by_cases hi:i=δi; swap; · rw [show (kz).coming i Q₀ z= _ from hz i hi Q₀ z]; exact (hX.cover _ Q₀ ht hy hv z).trans (mul_le_mul_of_nonneg_left (hP _) (Real.exp_pos _).le)
    subst i; exact ((he Q₀ z).trans (hp0 _ _)).trans (mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le)
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.angelic
#print axioms YM.MassiveQCD.Apron.Grove.heritage
