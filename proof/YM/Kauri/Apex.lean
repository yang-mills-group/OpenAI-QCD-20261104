import YM.Kauri.Utan
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat MeasureTheory
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
include J H JQ R S B
lemma semblance : ∃ g:Ortho.Skew,A.jet g ≠ 0:=by
     let g:= Omega 0; obtain ⟨F,hF⟩:=loans J H JQ B R 10 (by decide); refine ⟨g,fun h=> showtime R 0 ?_⟩; ext1 x; apply F.injective; rw [LinearMap.zero_apply,map_zero,hF.revenue]; exact Subtype.ext (by change A.jet g _= _; rw[h]; rfl)
variable {e β:ℝ}(hc:C.Path β e)(hP:P.System)(ht:Tendsto φ atTop atTop)
variable (hD:(swingE K 1).range=(bits K).range)(hμ:Module.finrank ℂ (obσ 1 K).range=22)(hV:Module.finrank ℂ (bits K).range=20)(hχ:∀ d,∃ n:Lattice.Side,Injective (P.candidate d n 0))
set_option quotPrecheck false
local notation "X0" => equip T ρ A.jet
open Physics
lemma tells: Physics.Ward (F:=equip T ρ A.jet) (fun a b=>W (a,b)) K.total:=by
     let V(a b:Axis):=W (a,b); constructor
     · intro n x hx q χ h v ht a b; exact termG_integrable V χ (fun z=> v (z-x 0)) x q JQ.h hx h a b ((EuclideanSpace.proj (𝕜:=ℝ) b).continuous.comp (ht.comp (continuous_id.sub continuous_const)))
     · intro n x hx q χ h a; let Q:=q 0; let v:=Fin.tail q; have hp: q=Fin.cons Q v:= (Fin.cons_self_tail q).symm
       have he:shell (F:=X0) V K.total x q χ (fun _=> basis a)= gradG V χ a x v Q:=by
                  rw [hp]; unfold gradG shell; apply congr_arg; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single a]; · simp[V,basis_eq]
                  · intro j _ hj; simp [V,basis_eq,hj,Ne.symm hj]
                  simp
       unfold V at he; rw [he,B.snaps _ _ _ _ hx h, heads]; rw [← wins J H JQ B R S]; change _= K.total _ _ (update q 0 (K.arc a Q)); rw[hp,Fin.update_cons_zero]
     intro n x hx q χ h g; let f:=q 0; let p:=Fin.tail q; have hp:q=Fin.cons f p:= (Fin.cons_self_tail q).symm
     change fluxG V χ (fun z=> M4.move g.val (z-x 0)) x q= K.total _ _ (update q 0 (A.jet g f)); rw [hp,Fin.update_cons_zero]; exact (A.relation g f n x χ hx h p).trans (heads p x _)
include hμ hV hD hc ht hP hχ
lemma shoots : Physics.Stress (equip T ρ A.jet) (fun a b=>W (a,b)):=by
      have hb:= S.acts JQ.h (loans J H JQ B R)
      let V(a b:Axis):= W (a,b)
      have hv (U:Momentum (equip T ρ A.jet)):Candidate (equip T ρ A.jet) U ↔ ∃ x y:ℂ,U=x • V+y • Physics.identity (equip T ρ A.jet):=by
               let M(i:Axis×Axis):K.W:= U i.1 i.2; have ht:= (constituted T M ρ A.jet hb).trans (chartered hc hP ht T H JQ hD hμ hV hχ W M J.n); change Candidate (equip T ρ A.jet) (fun i j=> M (i,j)) ↔ _; rw[ht]; constructor <;> (rintro ⟨x,y,h⟩; refine ⟨x,y,?_⟩)
               · funext i j; exact congr_fun h (i,j)
               funext i; exact congr_fun (congr_fun h i.1) i.2
      refine ⟨(constituted T W ρ A.jet hb).mpr ⟨J.n.tense,J.n.div⟩,(fun s a b=> arp J H JQ B R S hc hP ht hD hμ hV hχ s a b),?_,?_,?_,hv,?_,semblance J H JQ B R S⟩
      · intro a b i; have hh:= congr_fun (J.n.real'a i) (a,b); unfold roseC at hh; let c:ℂ:= ↑(signT (Signed.mirror i) a*signT (Signed.mirror i) b:ℝ); have he:c*c=1:=by unfold c; simp only[signT]; split <;> split <;> push_cast <;> norm_num
        change T.adj i (W (a,b))= _; have hn:T.adj i (W (a,b))= c • W (a,b):=by nth_rw 2 [←hh]; change _= c • c • _; rw[smul_smul,he,one_smul]
        rw[hn]; change c • _=_ • W (a,b); unfold c; by_cases hx:i=a<;> by_cases hy:i=b<;> simp [hx,hy,signT,Signed.mirror]
      · intro z h; apply J.n.non z; funext i; exact congr_fun (congr_fun h i.1) i.2
      · exact (hv _).mpr ⟨0,1,by rw [zero_smul,one_smul,zero_add]⟩
      change ∃ a,K.arc a≠0; by_contra! hf; have hx:divR K=0:=by
                  unfold divR; refine LinearMap.ext fun x=> funext fun i=> ?_; rw[LinearMap.pi_apply, LinearMap.sum_apply]; simp[hf]
      rw[←hD, swingE,hx,LinearMap.zero_comp,LinearMap.range_zero, finrank_bot] at hV; exact Nat.noConfusion hV
end YM.Kauri
#print axioms YM.Kauri.shoots
#print axioms YM.Kauri.tells
