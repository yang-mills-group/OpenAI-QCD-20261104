import YM.QCD.Cove.Aft
/-! # including FLAG-touch actual honour. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{f c: Side}{S: Ratio c f}{E D J: Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "I"=> Fj D E J
variable (g:Send S F D) (P:Rise f F E J)(t:ℝ) 

lemma flag_under {X T:Support f}{U V:Grid f}(ht:X⊆T)(h:T∩flags t U=T∩flags t V): X∩flags t U=X∩flags t V:=by
   rw [← inter_eq_left.mpr ht,inter_assoc,h, ← inter_assoc,inter_eq_left.mpr ht]

lemma hearing (hp:P.Wave t)(s:Finset I):UsesFinal t (brimW g P s) (fun U=>made P t U s):=by
  intro U V h H
  unfold made; apply congr_arg₂
  · apply prod_congr rfl; intro i hi
    have hx : (P.row i).support ⊆ brimW g P s:= fun j hj=> (native_sub g P s) (mem_biUnion.mpr ⟨Sum.inr (.inl i),by simpa [leftE] using hi,hj⟩)
    have he:=flag_under t hx H
    have hA: Healthy t (P.row i).support U ↔ Healthy t (P.row i).support V:=by simp only [Healthy, Finset.disjoint_iff_inter_eq_empty,he]
    rw [P.hype,P.hype]; simp only [hA,(hp.use i) U V (agrees_mono h hx)]
  apply prod_congr rfl; intro i hi
  have hx :(P.front i).place ⊆brimW g P s:=fun j hj=> (native_sub g P s) (mem_biUnion.mpr ⟨Sum.inr (.inr i),by simpa [spent] using hi,hj⟩)
  exact hp.oblige i _ _ (agrees_mono h hx) (flag_under t hx H)
lemma ax_loc (s:Finset I): LocalOn (coreW g P s:Set (Site f)) (fun U=> axle g U s):=by
   intro U V H; unfold axle; apply noncommProd_congr rfl; intro i hi; unfold bucks; exact congr_arg excess ((g.stance i) _ _ (agrees_mono H (fun j hj=> mem_biUnion.mpr ⟨Sum.inl i,by simpa [ops] using hi,hj⟩)))
lemma framed_eq (s:Finset I)(U V:Grid f)(h:Agrees (brimW g P s) U V)(x:Alg R)(hp:x∈ region (hooks S (coreW g P s))): wipe A B (g.shortP U) x=wipe A B (g.shortP V) x:=by
   let w:= hooks (F:=F) S (coreW g P s); have he : (wipe A B (g.shortP U)).comp (embed ((↑):↥w→R))=(wipe A B (g.shortP V)).comp (embed ((↑):↥w→R)):=by
     apply ext_atoms; intro ⟨i,hi⟩; simp only [AlgHom.comp_apply,embed_atom]
     rcases splits_index i with ⟨v,rfl⟩|⟨v,rfl⟩
     · rw [wiper,wiper]; apply sum_congr rfl; intro j _
       change ha c f F v∈ hooks _ _ at hi; rw [hooked,rootA] at hi; exact congr_arg (· • _) (g.shortens v j _ _ (agrees_mono h (show halo g.trim {locationP v}⊆brimW g P s from by rw [brim_eq]; exact Corona.halo_mono (by omega) (singleton_subset_iff.mpr hi)))) -- shortens lemma application maybe
     rw [tails,tails]
   obtain ⟨y,rfl⟩:=hp; exact DFunLike.congr_fun he y
lemma vetted (hp:P.Wave t)(s:Finset I): UsesFinal t (brimW g P s) (dye g P t s):=by
   intro U V H h; apply Subtype.ext; change light _ (dye g P t s U)=light _ (dye g P t s V); rw [dipping,dipping,show made P t U s=made P t V s from hearing g P t hp s _ _ H h,show axle g U s=axle g V s from ax_loc g P s U V (agrees_mono H (native_sub g P s))] -- ax_loc rewrite issue
   exact framed_eq g P s U V H _ (framed g P t s V hp)
lemma stillL (hp:P.Wave t)(s: Finset I): UsesFinal t (brimW g P s) (hue g P t s):=by
  intro U V H h; unfold hue closeS; rw [inter_comm (flags t U),h,inter_comm _ (flags t V)]; rw [vetted g P t hp s U V H h]

end YM.QCD.Cove
