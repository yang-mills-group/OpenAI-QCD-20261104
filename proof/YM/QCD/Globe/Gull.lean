import YM.QCD.Globe.Vernal
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
local notation "V"=> EvenA c N
local notation "Q"=> tied S h 0 1
variable (S h)
lemma cup (k:su.El):siteRot (fun _: Site c=>k)*Q*star (siteRot (fun _=>k))=Q:=by
     let p:Frame f:=fun _=>k; have he:gauge p (1:Grid f)=1:=by ext1 i; simp [p,Lattice.gauge];
     exact (gauges S h 0 1 p).symm.trans (congr_arg _ he)
set_option quotPrecheck false
local notation "M"=> sliceL S h
lemma joule (t:Strut c)(K:Spike)(g:Site f→ℂ)(hp:Warrant (raise (M) t) g K): haze t K (g ∘ (M).embed)*Q*star (haze (raise (M) t) K g)= Q:=by
     have he : (M).embed 0=0:=map_zero (M).root
     have hh : Glare t.1 ((M).embed 0) ((M).embed 0) ((M).embed t.2) g:=by rw [he]; exact hp.1
     have hv := Revolve.dual S h hh hp.2 1; dsimp only at hv; rw [he,show pull t.1 ((M).embed t.2) (1:Grid f)=1 from t_one (raise (M) t)] at hv; exact hv.symm
lemma temperQ (P:Plan j)(D:Sheet f)(hp: Tempo D) : Tempo (1 - Q * (father S h + D)⁻¹ * (Q)ᴴ):= by
     have he : (M).embed 0=0:=map_zero (M).root
     rw [← tree_zero P]; refine ⟨?_,?_,?_⟩
     · intro k p
       have hh:gauge (fun _: Site f=>k) (1:Grid f)=1:=by ext1 i; simp [Lattice.gauge]
       unfold vaultF; rw [← show sunny P S.wing f=wood P (0:Site f) S.wing 1 from rfl]
       have H:= Orbit.momentum (sunny P S.wing f + (Q)ᴴ*Q + D) (siteRot (fun _=>k)) (siteRot p) (Q) (siteRot_u ..) (siteRot_u ..); dsimp only at H; unfold p at * -- edit
       erw [cup S h k] at H; rw [H.2,aura_add,aura_add,(savior P S.wing).hues k, H.1,hp.hues k]
     · intro i g k hi; obtain ⟨p,ht,rfl⟩:= sheetsX M i k g hi
       let w:=raise M i; unfold vaultF; rw [← show sunny P S.wing f=wood P (0:Site f) S.wing 1 from rfl]; let X:= haze w k p; let K:=sunny P S.wing f
       have H:= Orbit.momentum (K+(Q)ᴴ*Q+D) X (haze i k (p ∘ (M).embed)) (Q) (trail hi) (trail ht); dsimp only at H; unfold X at H; unfold w at *; rw [joule S h i k p ht] at H; change _=1-Q*(K+(Q)ᴴ*Q+D)⁻¹*(Q)ᴴ; rw [H.2, aura_add,aura_add,(savior P S.wing).turns _ p k ht,H.1,hp.turns _ p k ht]
     exact Orbit.newborn_s S P h (D:=fun _=>D) _ hp.song
-- sheath auth: can permit prefactor complex, zero-coef log chosen.
lemma weather (X: EvenA f N)(Y:V)(hp:Cocoa X)(z:ℂ)(hz:z ≠0)(ht: sheath 1 (choir N (Q)) (exp X.val)= z • exp Y.val)(he:coef ∅ Y.val=0): Cocoa Y:=by
    let A:=choir N (Q)
    have hh (T:Matrix (Modes f N) (Modes f N) ℂ)(P:Matrix (Modes c N) (Modes c N) ℂ)(hT:T∈unitary _)(hP:P∈unitary _)(hX:sways T X=X)(hA:P*A*star T=A): sways P Y=Y:=by
         have hU:=Kit.compat hT hP 1 A (exp X.val); rw [hA,map_weight,show disguise T X.val=X.val from congr_arg Subtype.val hX] at hU; unfold A at hU; rw [ht,map_smul,map_weight] at hU
         apply Subtype.ext; exact submerged (sways P Y).val Y.val 1 (sways P Y).2 Y.2 ((smul_right_injective _ hz hU).trans (one_smul _ _).symm) (Stew.vacant P Y.val)
    refine ⟨fun i hi=> ?_,fun k=> ?_,fun i g k hy=> ?_,?_⟩
    · let G:= flute (Lat.Row f) i; let H:= flute (Lat.Row c) i
      apply hh G H (unit_f hi) (unit_f hi) (hp.flavorG i hi); rw [show H*A= A*G from column _ _,Matrix.mul_assoc, (show G*star G=1 from (unit_f hi).2),Matrix.mul_one] -- name
    · apply hh (Lat.rotates N (fun _=>k)) (Lat.rotates N (fun _=>k)) (Lat.rotates_law ..) (Lat.rotates_law ..) (hp.choco k); unfold Lat.rotates; rw [← copies_star,← replicas,← replicas,← choir_mul,← choir_mul]; exact congr_arg (choir N) (cup S h k)
    · obtain ⟨p,hp',rfl⟩:=sheetsX M i k g hy; let j:=raise M i; let G:= haze j k p; let H:=haze i k (p ∘ (M).embed)
      apply hh (copies N G) (copies N H) (copies_unitary _ _ (trail hp')) (copies_unitary _ _ (trail hy)) (hp.cream _ _ _ hp'); rw [← copies_star]; unfold A; rw [← replicas,← replicas,← choir_mul,← choir_mul, show H*Q*star G=Q from joule S h i k p hp'] -- dot
    have hA:idol c N*A*star (idol f N)=A:=by unfold A idol; rw [← copies_star,← replicas,← replicas,← choir_mul,← choir_mul]; congr 1; change chirality c * Q * star (chirality f)=Q; have he:chirality c*Q=Q*chirality f:= Eq.symm (tiedSpin ..); rw [he, Matrix.mul_assoc,chi_star,chi_sq,Matrix.mul_one]
    have hv:=Kit.compat (Sway.white (F:=N) (f:=f)) (Sway.white (F:=N) (f:=c)) 1 A (surf _ (exp X.val)); rw [hA,← shoot,surfS,map_weight, show disguise _ (surf _ X.val)=X.val from congr_arg Subtype.val hp.real] at hv; unfold A at hv; rw [ht,map_smulₛₗ,map_smul,surfS,map_weight] at hv
    have hz : star z ≠ 0:= star_ne_zero.mpr hz
    apply Subtype.ext; apply submerged (Regal c N Y).val Y.val ((star z)⁻¹*z) (Regal c N Y).2 Y.2
    · rw [mul_smul,← hv,smul_smul]; change _=((star z)⁻¹*star z) • _; rw [inv_mul_cancel₀ hz,one_smul]; rfl
    rw [he]; exact (Reggae.yours Y).trans ((congr_arg star he).trans (star_zero _))
end YM.QCD.Globe
