import YM.QCD.Door.Slope
/-! # Anti-Hermitian star chirality transform. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks OrbitG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{j k:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}{F:ℕ}
local notation "S"=> sliceL L H
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {G:Grid f→Sheet f}{δ a b c' q:ℝ}{l:ℕ} (P:Sun L c f H δ a b c' q l G)

def idol (f: Side) (F:ℕ):Matrix (Modes f F) (Modes f F) ℂ:= copies F (chirality f)
lemma starI: star (idol f F)=idol f F:=by unfold idol; rw [← copies_star, chi_star]
lemma idea: idol f F*idol f F=1:=by unfold idol; rw [← copies_mul,chi_sq,copies_one]
lemma white: idol f F∈unitary _:= ⟨by rw [starI,idea],by rw [starI,idea]⟩
lemma duality {M:ArrayL (Site f) (Site c)} {N: ArrayL (Site c) (Site f)} (F:ℕ)(h:N=foldH M): choir F Mᴴ=idol c F*choir F N*star (idol f F) ∧ choir F Nᴴ=idol f F*choir F M*star (idol c F):=by
 rw [starI,starI,h]; unfold foldH; have he (n:Side):terraL (Site n)=chirality n:=rfl
 rw [he,he]; unfold idol; simp only [← replicas,← choir_mul]; constructor
 · simp [← Matrix.mul_assoc,chi_sq]; rw [Matrix.mul_assoc,chi_sq, Matrix.mul_one]
 rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; rw [← Matrix.star_eq_conjTranspose, chi_star, ← Matrix.star_eq_conjTranspose, chi_star, Matrix.mul_assoc] -- fill
lemma surge (C D:Type*)[Fintype C][Fintype D](x:Dirac C):surf _ (near C D x)=near C D (surf C x):=by
  have hp (L: List _): surf _ (near C D (L.map atom).prod)=near C D (surf C (L.map atom).prod):=by
     induction L with
     | nil=> simp [surf_one]
     | cons j L ih=> rw [List.map_cons,List.prod_cons,map_mul,surf_mul,surf_mul,map_mul,ih]; congr 1
                     cases j
                     next i=> change surf _ (pass _ (psi _))= pass _ (surf _ (psi _)); rw [pass_psi,surf_P,surf_P,pass_bar]
                     next i=> change surf _ (pass _ (bar _))=pass _ (surf _ (bar _)); rw [pass_bar,surf_M,surf_M,map_neg,pass_psi]
  have he s: surf _ (near C D (mono s))=near C D (surf _ (mono s)):=by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa only [List.map_ofFn] using hp (List.ofFn w)
  rw [← write x]; simp_rw [map_sum,map_smul,map_smulₛₗ,RingHom.id_apply,he]

lemma amber (F b:ℕ)(U:Grid f)(hv: Sacred P):
    let p:=idol f F; let q:=idol c F
    Usher S (P.equip F b) U U (dawn (whole p q)) (dawn p) (dawn q) (Equiv.refl _) (Equiv.refl _):=by
 intro p q; refine ⟨fun i j=>rfl,fun i=>Finset.image_id.symm, fun i x=> ?_,fun x=>?_,fun x=> ?_⟩
 · cases i
   next i=>
    let H := choir F (flowY P i U); change disguise (whole p q) (surf _ (excess (pond (head _ _) H) x))=excess (pond _ H) _; rw [pondY, show star H=p*H*star p from ?_]; exact pondD ..
    unfold H; simp only [Matrix.star_eq_conjTranspose,← choir_star]; exact (duality (M:=flowY P i U) F (glyph hv i U)).1
   next i=>
    let T:=choir F (heads P b i U); let D:= choir F (tailsF P b i U); change disguise (whole p q) (surf _ (excess (bark (bladesF T D)) x))=excess (bark (bladesF T D)) _; rw [barkY]; rw [show Dᴴ=p*T*star q from (choir_star _ _).symm.trans (duality _ (grim b hv i U)).2, show Tᴴ=q*D*star p from (choir_star _ _).symm.trans (duality _ (grim b hv i U)).1]; exact barkA p q T D white white _ -- syntax
 · change disguise (whole p q) (surf _ (near _ _ x))=near _ _ _; rw [surge,partitioned]; rfl
 rw [sea_eq]; change disguise q (surf _ _)=wipe _ _ _ _; rw [barkZ,← choir_star,← choir_star,(duality _ (wising b hv U)).1,(duality _ (wising b hv U)).2]; exact barkW p q _ _ white white _ -- check
end YM.QCD.Sway
