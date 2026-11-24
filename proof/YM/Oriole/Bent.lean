import YM.Oriole.Rhea
import YM.Tinus.Wreath
import YM.Tinus.Screws
/-! Actual symmetries on the axial report.Least Primary.Money Tally. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder Kronecker
variable {S:Scheme}{c R:Side}{i l n F d:ℕ}(A:Massive.Run S n R 6)
variable (r:PCAC.Herald)(a b:Flavor 6)
open Massive.Patria Massive.Patria.Depth QCD.Tide Exposure PCAC Cylinder TorusPCAC.Geometry
open UV Finset QCD.Revolve Rolls
variable (u:Averaging)(x y:Spike)(w:EuPin)(s:Signed)(p:Bool)(z:ℂ)(f:FlavorTorus)
local notation "κ"=> paidM a b f
lemma off_char (v:Site c) (Y:Lat.Fields c 6) : let C:= adapter (byFlavor f fun i:Modes c 6=> i.2) (byFlavor f⁻¹ fun i:Modes c 6=>i.2); let W:=localF v x a b; C (applyMark p W Y) = applyMark p (κ • W) (C Y):=by
    intro C W; let P:= byFlavor f fun i:Modes c 6=>i.2; let Q:=byFlavor f⁻¹ fun i:Modes c 6=>i.2; apply Eq.symm; apply L_slope p P Q
    · ext i j; unfold P byFlavor; rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,smul_eq_mul]; by_cases h:i.2=a∧j.2=b
      · simp only; rw [h.1,h.2]; unfold paidM; let V:ℂ:= (f a).val; let v:ℂ:= (f b).val; calc
            _=(V*star V) * (v* W i j):=by ring
            _= W i j*v:=by rw [(show V*star V=1 from (f a).property.2)]; ring
      rw [show W i j=0 from by unfold W localF; rw [zleft]; unfold flavorW; simp [spot,h]]; ring
    ext i j; unfold Q; rw [byFlavor,Matrix.diagonal_transpose, Matrix.diagonal_mul,Matrix.mul_diagonal, Matrix.smul_apply]; by_cases h:i.2=a ∧ j.2=b
    · rw[h.1,h.2]; let V:ℂ:= (f a).val; let v:ℂ:= (f b).val; change star V*v* W i j*star v=star V*W i j; calc
            _=(v*star v)*(star V*W i j):=by ring
            _= _:=by rw [show v*star v=1 from (f b).property.2,one_mul]
    rw [show W i j=0 from by unfold W localF; rw [zleft]; unfold flavorW; simp [spot,h]]; simp
lemma lspin (B:Lat.Fields c 6)(D:Sour (Modes c 6)): applyMark p (z • D) B=z • applyMark p D B:=by cases p <;> simp only [column,row,Matrix.smul_apply,smul_eq_mul,mul_smul,smul_sum] -- exact
noncomputable abbrev regH : Cover → Insertion (S.side R i) 6:= stalk x A a b p i -- i implicit.Run
variable (h:A.Actual) (hi:i≤ l)(hl:l≤ n)
local notation "U₀"=> stalk x A a b p l
local notation "F₁"=> report A U₀ u
open Poised Poised.Beacon
local notation "iso"=>MassFields.isotropic
include h hl
lemma glint0(m:Cover): Action.flavor f (⇑(U₀ m))=κ • ⇑(U₀ m):=by
      funext U; let Y:=actor A l; have ht: Action.flavor f (⇑Y)= ⇑Y:=by unfold Y; rw [act A h hl,pier A h hl]; exact (Depth.arrives A l hl).2.2.1 f
      change adapter _ _ _ = _; change adapter _ _ (applyMark _ _ (Y U))=κ • applyMark p _ (Y U)
      nth_rw 2 [← show Action.flavor f (⇑Y) U= Y U from congr_fun ht U]; exact (off_char a b x p f (wrap _ m) _).trans (lspin ..)
include hi
private abbrev spy {c: Side}(F:Lat.Fields c 6→ₐ[ℂ] Lat.Fields c 6)(V:Grid c): Insertion c 6 →ₗ[ℝ] Lat.Fields c 6:= ((F.toLinearMap).comp (ContinuousMap.evalCLM ℂ V).toLinearMap).restrictScalars ℝ -- no includes
lemma glint1 : Action.flavor f (⇑(F₁ i 0))=κ • ⇑(F₁ i 0):=by
      let X0:=visitor S l i u 0 U₀; let B(b): Insertion (S.side R l) 6:=κ • U₀ b
      have hB: Action.flavor f (⇑X0)= ⇑(κ • X0):=by
           funext U; unfold X0 visitor; rw [smul_zero]; have he:= permeate u 1 (spy (Lining.Temper.stroll _ f) U) (U₀) B U (fun i=>by rw [Signed.act_one]; exact congr_fun (glint0 A a b x p f h hl i) U) (odd_to (S:=S) hi); rw[permit_one] at he; have hu : Averaging.filter u (ratioTo S l i) B 0=κ • Averaging.filter u (ratioTo S l i) U₀ 0:=by
                   rw [roles,roles]; let L:= (κ • (LinearMap.id (R:=ℂ) (M:=Insertion (S.side R l) 6))).restrictScalars ℝ; exact Eq.symm (rollLinear (l:=menu u) (M:=ratioTo S l i) (k:=1) U₀ 0 L)
           rw [hu] at he; exact he
      change Action.flavor f (⇑(relay A i X0))=κ • ⇑(relay A i X0)
      let Y:=κ • X0; suffices Action.flavor f (⇑(relay A i X0))= ⇑(relay A i Y) by rw[this]; unfold Y relay; rw [map_smul]; rfl
      change Action.flavor f (⇑X0)=⇑Y at hB; clear_value Y; clear_value X0 -- hB uses κ•X0 def not Y. adjust
      induction hi using Nat.decreasingInduction with
      | self=> unfold relay; rw [S.entrance]; exact hB
      | of_succ i h' ih => rw [stepped A X0 h',stepped A Y h']; unfold Run.block; rw [step_brute,step_brute]; rw [flavor_shift _ _ (S.admissible i) _ _ (ContinuousMap.continuous _),ih]
omit hi
include h hl
lemma turn0 (b':Cover)(hp:w.Lifts s)(hz:conjug w x=y): Action.pin w s (⇑(U₀ b'))= ⇑(stalk y A a b p l (s.act b')):=by
      funext V; let T:=actor A l; let c:=S.side R l; let g:=Patria.prism s (c:=c); let B:= pull (K:=su.El) s (0:Site c) V; let t:= wrap (S.side R l) b'; let σ:= wrap c (s.act b'); have ht:Action.pin w s (⇑T)=⇑T:=by unfold T; rw[act A h hl,pier A h hl]; exact (Depth.arrives A l hl).1 w s hp
      have he:star w.matrix.val*y=x*star w.matrix.val:=by rw [← hz,conjug,←mul_assoc,←mul_assoc,w.isUnitary.1,one_mul, E_star]
      rw [Patria.pinned]; have hP:σ=shiftE s 0 t:=by unfold σ; rw [← wrap_signed]; exact Eq.symm (add_zero _)
      change Kit.disguise _ (ore t p a b x (T B))=ore σ p a b y (T V); rw [hP]; rw [← show Action.pin w s (⇑T) V=T V from congr_fun ht V, Patria.pinned]; exact (L_hue a b t x p _ s g w.matrix.val 0 0 (Patria.smoke s) (EuPin.retains _ hp) y he _).symm
lemma powerF (v:Site c): localF v (z • x) a b=z • localF v x a b:=by -- h unused omit
      unfold localF flavorW onSpin; rw [waveP,show ∀ (X:Bundle),rides (Equiv.refl (Site c)) (fun _=> z • X)=z • rides (Equiv.refl _) (fun _=>X) from ?_]; rw [Matrix.smul_kronecker,Matrix.mul_smul]; intro X; ext i j; simp [Lat.rides, ite_smul,smul_ite]
include hi
lemma turn1(hp:w.Lifts s)(hz:conjug w x=z • x) : Action.pin w s (⇑((report A U₀ iso) i 0))= z • ⇑(report A U₀ iso i 0):=by
    let X0:= visitor S l i iso 0 U₀; let L(m):Insertion (S.side R l) 6:=z • U₀ m
    have ht:Action.pin w s (⇑X0)= ⇑(z • X0):=by
         funext V; unfold X0 visitor; rw[smul_zero]
         have hx(m): Action.pin w s (⇑(U₀ m))= ⇑(L (s.act m)):=by rw[turn0 A _ _ x (z • x) w s p h hl m hp hz]; funext U; change applyMark p (localF _ _ _ _) _= z • applyMark p _ _; rw[powerF (A:=A) a b x z h hl,lspin]
         have he:= permeate iso s (spy (Lining.Temper.shipP _ s w) (pull s 0 V)) U₀ L _ (fun m=>congr_fun (hx m) V) (odd_to (S:=S) hi); rw[show Averaging.permute s iso=iso from rfl] at he; rw [show Averaging.filter iso (ratioTo S l i) L 0=z • Averaging.filter iso (ratioTo S l i) U₀ 0 from ?_] at he; exact he
         rw [roles,roles]; let W:=(z • (LinearMap.id (R:=ℂ) (M:=Insertion (S.side R l) 6))).restrictScalars ℝ; exact Eq.symm (rollLinear (l:=menu iso) (M:=ratioTo S l i) (k:=1) U₀ 0 W)
    change Action.pin w s (⇑(relay A i X0))= z • ⇑(relay A i X0); let Y:=z • X0; suffices Action.pin w s (⇑(relay A i X0))= ⇑(relay A i Y) by rw [this]; unfold Y relay; rw [map_smul]; rfl
    change Action.pin w s (⇑X0)=⇑Y at ht; clear_value Y; clear_value X0
    induction hi using Nat.decreasingInduction with
    | self=> unfold relay; rw [S.entrance]; exact ht
    | of_succ i h ih => rw [stepped A X0 h,stepped A Y h]; unfold Run.block; rw [step_brute,step_brute]; rw[pin_travel _ _ _ _ hp (S.admissible i) _ _ (ContinuousMap.continuous _),ih]
-- input charged panel.Tally.
variable (v:Label d)(H:SourceRead.TaperHol)(W:RawSym)(B:Bore d)(Q:Market S R d)(hW: Wager A H B Q i)(hb:Rubric W B)(hT:Tally H 0 v (A.density i) (⇑(report A (stalk x A a b p l) u i 0)))
include hT hb hW
lemma C_view : CharmC a b v.val:=by
      intro u'; let g:=W.flavor d u'; have ht:g v=paidM a b u' • v:=by
          have hx:= Depth.arrives A i hW.siteM; have hv:=Canvas.arrows H u' _ (g v) (fun x:Label d=>⇑(B (S.side R i) 0 x)) hT hW.reading (by rw[pier A h hW.siteM]; exact hx.2.2.1 u') (hb.flavor (S.side R i) v 0 u'); rw [show Action.flavor u' _ = _ from glint1 A a b u x p u' h hi hl] at hv; exact Canvas.consensus _ _ _ hv _ (QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.Talent.shines H d 0 v (paidM a b u') (A.density i) _ hT)
      rw[←W.flavorActs,show W.flavor d u' v=_ from ht]; rfl
lemma W_view (y:Bool)(hy:x=pulp y)(hU:u=iso): Wings y v.val:=by
      subst x u; intro P s hP z hΓ; let g:=W.pin d P; have ht:g v=z • v:=by
          have hv:= Canvas.hinge s H P _ hP hW.living (g v) (fun x:Label d=>⇑(B (S.side R i) 0 x)) hT hW.reading (by rw [pier A h hW.siteM]; exact (Depth.arrives A i hW.siteM).1 _ _ hP) (by have h:= hb.pin (S.side R i) v 0 s P hP; rw[Signed.act_zero] at h; exact h)
          rw [turn1 A a b (pulp y) P s p z h hi hl hP hΓ] at hv; exact Canvas.consensus _ _ _ hv _ (QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby.Talent.shines H d 0 v z (A.density i) _ hT)
      rw[← W.pinActs,show W.pin d P v= _ from ht]; rfl
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.C_view
#print axioms YM.Massive.Oriole.W_view
