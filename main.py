"""
APS - SISTEMA DE IDENTIFICACAO E AUTENTICACAO BIOMETRICA
Cofre do Ministerio do Meio Ambiente: senha + reconhecimento facial, 3 niveis de acesso.

PROJETO DIDATICO: nao possui prova de vida (liveness). Uma foto ou video pode enganar
o reconhecimento. NAO use para proteger instalacoes ou informacoes reais.

Dependencias (terminal do VS Code):
    pip uninstall -y opencv-python opencv-python-headless
    pip install opencv-contrib-python numpy
Execucao:
    python main.py

Preservacao de dados: o banco aps_biometria.db e a pasta rostos NUNCA sao apagados ou
recriados. Antes de qualquer migracao de estrutura e feita uma copia de seguranca
(aps_biometria.db.backup_AAAAMMDD_HHMMSS). Rostos substituidos ou removidos vao para a
pasta rostos_arquivo. Backups existentes nunca sao tocados.
"""
import hashlib
import math
import os
import re
import secrets
import shutil
import sqlite3
import sys
import tkinter as tk
from contextlib import contextmanager
from datetime import datetime, timedelta
from tkinter import messagebox, simpledialog, ttk

import cv2
import numpy as np

# =========================================================
# CONFIGURACOES
# =========================================================
PASTA = os.path.dirname(os.path.abspath(__file__))
BANCO = os.path.join(PASTA, "aps_biometria.db")
PASTA_ROSTOS = os.path.join(PASTA, "rostos")
PASTA_ARQUIVO = os.path.join(PASTA, "rostos_arquivo")
ARQ_CODIGO_INICIAL = os.path.join(PASTA, "codigo_inicial_ministro.txt")
CASCADE_LOCAL = os.path.join(PASTA, "haarcascade_frontalface_default.xml")

AMOSTRAS_CADASTRO = 30      # fotos do rosto no cadastro
TAMANHO_ROSTO = (200, 200)  # tamanho do recorte (igual ao projeto original)
LIMIAR_LBPH = 60.0          # menor = mais parecido. CALIBRE testando com o grupo
QUADROS_APROVACAO = 8       # quadros SEGUIDOS aprovados para liberar o acesso
QUADROS_MAXIMOS = 200       # tempo maximo da tentativa de verificacao
QUADROS_MAX_CADASTRO = 1800 # tempo maximo da captura de cadastro (~1 minuto)
MAX_FALHAS = 3              # falhas consecutivas ate bloquear a conta
BLOQUEIO_MINUTOS = 5        # duracao do bloqueio temporario
MAX_FALHAS_CODIGO = 5       # erros do codigo inicial ate gerar um codigo novo

ITER_LEGADO = 200000        # iteracoes PBKDF2 do projeto original
ITER_ATUAL = 600000         # iteracoes PBKDF2 para novas senhas / migracao

DEBUG = os.environ.get("APS_DEBUG") == "1"  # imprime distancias no console (calibracao)

NIVEIS = {
    1: "Funcionario Geral",
    2: "Diretor de Divisao",
    3: "Ministro do Meio Ambiente",
}

PERMISSOES = {
    1: ["Consultar informacoes gerais"],
    2: ["Consultar informacoes gerais",
        "Consultar funcionarios",
        "Consultar registros de acesso"],
    3: ["Consultar informacoes gerais",
        "Consultar funcionarios",
        "Consultar registros de acesso",
        "Cadastrar funcionarios e definir niveis",
        "Remover funcionarios, recadastrar rostos e redefinir senhas",
        "Desbloquear contas",
        "Painel exclusivo do Ministro"],
}

MSG_LOGIN_INVALIDO = "Usuario ou senha incorretos."
REGEX_USUARIO_NOVO = re.compile(r"^[a-z0-9_-]{3,30}$")

# Colunas que o sistema usa. As que faltarem no banco antigo sao ADICIONADAS (nunca recriadas).
COLUNAS_FUNCIONARIOS = {
    "nome": "TEXT NOT NULL DEFAULT ''",
    "senha_hash": "TEXT NOT NULL DEFAULT ''",
    "salt": "TEXT NOT NULL DEFAULT ''",
    "ativo": "INTEGER NOT NULL DEFAULT 1",
    "falhas": "INTEGER NOT NULL DEFAULT 0",
    "bloqueado_ate": "TEXT",
    "iteracoes": "INTEGER NOT NULL DEFAULT %d" % ITER_LEGADO,
}
COLUNAS_REGISTROS = {
    "usuario": "TEXT NOT NULL DEFAULT ''",
    "evento": "TEXT NOT NULL DEFAULT ''",
    "data_hora": "TEXT NOT NULL DEFAULT ''",
}
COLUNAS_VITAIS_FUNCIONARIOS = ("id", "usuario", "nivel")  # sem elas o banco nao e utilizavel


# =========================================================
# BANCO DE DADOS (com migracao segura do banco antigo)
# =========================================================
@contextmanager
def banco():
    con = sqlite3.connect(BANCO)
    con.row_factory = sqlite3.Row
    try:
        yield con
        con.commit()
    except Exception:
        con.rollback()
        raise
    finally:
        con.close()


def _tabela_existe(con, tabela):
    return con.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name = ?",
                       (tabela,)).fetchone() is not None


def _colunas(con, tabela):
    return {linha["name"] for linha in con.execute("PRAGMA table_info(%s)" % tabela)}


def fazer_backup_banco():
    """Copia o banco para um arquivo novo (nunca sobrescreve backups existentes)."""
    carimbo = datetime.now().strftime("%Y%m%d_%H%M%S")
    destino = "%s.backup_%s" % (BANCO, carimbo)
    contador = 1
    while os.path.exists(destino):
        destino = "%s.backup_%s_%d" % (BANCO, carimbo, contador)
        contador += 1
    origem = sqlite3.connect(BANCO)
    copia = sqlite3.connect(destino)
    try:
        origem.backup(copia)
    finally:
        copia.close()
        origem.close()
    return destino


def inicializar_banco():
    """
    1) Se o banco ja existe: confere integridade e estrutura SEM alterar nada.
    2) Se faltar coluna: faz backup e so entao adiciona as colunas (ALTER TABLE ADD COLUMN).
    3) Cria apenas tabelas que nao existem. Nenhum dado e apagado.
    """
    os.makedirs(PASTA_ROSTOS, exist_ok=True)
    if os.path.isfile(BANCO) and os.path.getsize(BANCO) > 0:
        faltam = False
        with banco() as con:
            if con.execute("PRAGMA quick_check").fetchone()[0] != "ok":
                raise RuntimeError("O arquivo aps_biometria.db parece danificado. "
                                   "Nada foi alterado. Restaure um backup.")
            if _tabela_existe(con, "funcionarios"):
                existentes = _colunas(con, "funcionarios")
                ausentes_vitais = [c for c in COLUNAS_VITAIS_FUNCIONARIOS if c not in existentes]
                if ausentes_vitais:
                    raise RuntimeError("Estrutura inesperada na tabela funcionarios (faltam: %s). "
                                       "Nada foi alterado." % ", ".join(ausentes_vitais))
                faltam = any(c not in existentes for c in COLUNAS_FUNCIONARIOS)
            if _tabela_existe(con, "registros"):
                faltam = faltam or any(c not in _colunas(con, "registros")
                                       for c in COLUNAS_REGISTROS)
        if faltam:
            fazer_backup_banco()

    with banco() as con:
        con.execute("""
            CREATE TABLE IF NOT EXISTS funcionarios (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                nome TEXT NOT NULL,
                usuario TEXT NOT NULL UNIQUE,
                senha_hash TEXT NOT NULL,
                salt TEXT NOT NULL,
                nivel INTEGER NOT NULL CHECK(nivel BETWEEN 1 AND 3),
                ativo INTEGER NOT NULL DEFAULT 1,
                falhas INTEGER NOT NULL DEFAULT 0,
                bloqueado_ate TEXT,
                iteracoes INTEGER NOT NULL DEFAULT %d
            )
        """ % ITER_LEGADO)
        con.execute("""
            CREATE TABLE IF NOT EXISTS registros (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                usuario TEXT NOT NULL,
                evento TEXT NOT NULL,
                data_hora TEXT NOT NULL
            )
        """)
        con.execute("""
            CREATE TABLE IF NOT EXISTS configuracao (
                chave TEXT PRIMARY KEY,
                valor TEXT NOT NULL
            )
        """)
        for tabela, colunas in (("funcionarios", COLUNAS_FUNCIONARIOS),
                                ("registros", COLUNAS_REGISTROS)):
            existentes = _colunas(con, tabela)
            for coluna, definicao in colunas.items():
                if coluna not in existentes:
                    con.execute("ALTER TABLE %s ADD COLUMN %s %s" % (tabela, coluna, definicao))


def registrar_evento(usuario, evento):
    """Grava no log de auditoria. Nunca grava senhas."""
    try:
        with banco() as con:
            con.execute("INSERT INTO registros (usuario, evento, data_hora) VALUES (?, ?, ?)",
                        (usuario, evento, datetime.now().strftime("%d/%m/%Y %H:%M:%S")))
    except sqlite3.Error:
        pass


# ---------- senhas (PBKDF2-HMAC-SHA256 com salt individual) ----------
def gerar_hash(senha, salt=None, iteracoes=ITER_ATUAL):
    if salt is None:
        salt = secrets.token_hex(16)
    resultado = hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"),
                                    salt.encode("utf-8"), iteracoes).hex()
    return resultado, salt


def conta_tem_credencial(func):
    return bool((func["salt"] or "").strip() and (func["senha_hash"] or "").strip())


def validar_senha(senha, func):
    """Aceita o formato do projeto original (PBKDF2-SHA256, 200 mil iteracoes, salt em hex)
    e o formato atual (iteracoes guardadas na coluna 'iteracoes')."""
    if not conta_tem_credencial(func):
        return False
    try:
        iteracoes = int(func["iteracoes"] or ITER_LEGADO)
        calculado, _ = gerar_hash(senha, func["salt"], iteracoes)
        return secrets.compare_digest(calculado, func["senha_hash"].strip().lower())
    except (ValueError, TypeError, OverflowError):
        return False


def migrar_hash_se_preciso(usuario, senha):
    """Apos autenticacao valida, sobe contas antigas (200 mil iteracoes) para o padrao atual."""
    func = buscar_funcionario(usuario)
    if func is None or int(func["iteracoes"] or ITER_LEGADO) >= ITER_ATUAL:
        return
    novo_hash, novo_salt = gerar_hash(senha)
    with banco() as con:
        con.execute("UPDATE funcionarios SET senha_hash=?, salt=?, iteracoes=? WHERE usuario=?",
                    (novo_hash, novo_salt, ITER_ATUAL, func["usuario"]))


# ---------- consultas basicas ----------
def buscar_funcionario(usuario):
    with banco() as con:
        return con.execute("SELECT * FROM funcionarios WHERE usuario = ?",
                           ((usuario or "").strip().lower(),)).fetchone()


def existe_ministro():
    with banco() as con:
        return con.execute("SELECT COUNT(*) FROM funcionarios WHERE nivel = 3 AND ativo = 1"
                           ).fetchone()[0] > 0


def total_funcionarios():
    with banco() as con:
        return con.execute("SELECT COUNT(*) FROM funcionarios").fetchone()[0]


# ---------- bloqueio temporario (persistido no SQLite) ----------
def segundos_de_bloqueio(func):
    if not func["bloqueado_ate"]:
        return 0
    try:
        ate = datetime.strptime(func["bloqueado_ate"], "%Y-%m-%d %H:%M:%S")
    except ValueError:
        return 0
    return max(0, int((ate - datetime.now()).total_seconds()))


def registrar_falha(usuario):
    """Soma uma falha consecutiva. Ao chegar em MAX_FALHAS bloqueia por BLOQUEIO_MINUTOS."""
    with banco() as con:
        con.execute("UPDATE funcionarios SET falhas = falhas + 1 WHERE usuario = ?", (usuario,))
        linha = con.execute("SELECT falhas FROM funcionarios WHERE usuario = ?",
                            (usuario,)).fetchone()
        if linha and linha["falhas"] >= MAX_FALHAS:
            ate = (datetime.now() + timedelta(minutes=BLOQUEIO_MINUTOS)).strftime("%Y-%m-%d %H:%M:%S")
            con.execute("UPDATE funcionarios SET falhas = 0, bloqueado_ate = ? WHERE usuario = ?",
                        (ate, usuario))
            return True
    return False


def zerar_falhas(usuario):
    with banco() as con:
        con.execute("UPDATE funcionarios SET falhas = 0, bloqueado_ate = NULL WHERE usuario = ?",
                    (usuario,))


# =========================================================
# AUTORIZACAO (validada dentro de cada funcao, nao so na interface)
# =========================================================
def obter_ator(usuario):
    """Reconsulta o usuario no banco: o nivel vem SEMPRE do banco, nunca da tela."""
    func = buscar_funcionario(usuario) if usuario else None
    if func is None or not func["ativo"]:
        raise PermissionError("Sessao invalida. Entre novamente.")
    return func


def exigir_nivel(usuario, minimo, acao):
    ator = obter_ator(usuario)
    if ator["nivel"] < minimo:
        registrar_evento(ator["usuario"], "ACESSO NEGADO: " + acao)
        raise PermissionError("Permissao insuficiente: esta acao exige nivel %d." % minimo)
    return ator


# =========================================================
# CODIGO INICIAL DO MINISTRO (uso unico, fluxo controlado de primeiro acesso)
# =========================================================
def _config_get(con, chave):
    linha = con.execute("SELECT valor FROM configuracao WHERE chave = ?", (chave,)).fetchone()
    return linha["valor"] if linha else None


def _config_set(con, chave, valor):
    con.execute("INSERT OR REPLACE INTO configuracao (chave, valor) VALUES (?, ?)", (chave, valor))


def _normalizar_codigo(codigo):
    return re.sub(r"[\s-]", "", (codigo or "")).upper()


def _codigo_bate(codigo):
    """Compara com o codigo guardado (hash) SEM contar tentativa."""
    with banco() as con:
        h = _config_get(con, "codigo_hash")
        salt = _config_get(con, "codigo_salt")
    if not h or not salt:
        return False
    calculado, _ = gerar_hash(_normalizar_codigo(codigo), salt)
    return secrets.compare_digest(calculado, h)


def _arquivo_codigo_confere():
    try:
        with open(ARQ_CODIGO_INICIAL, encoding="utf-8") as arq:
            texto = arq.read()
    except OSError:
        return False
    achado = re.search(r"\b[0-9A-F]{4}-[0-9A-F]{4}\b", texto)
    return bool(achado) and _codigo_bate(achado.group(0))


def gerar_codigo_inicial():
    """Cria um codigo novo de uso unico, grava o hash no banco e o texto em arquivo local."""
    bruto = secrets.token_hex(4).upper()
    codigo = bruto[:4] + "-" + bruto[4:]
    h, salt = gerar_hash(_normalizar_codigo(codigo))
    with banco() as con:
        _config_set(con, "codigo_hash", h)
        _config_set(con, "codigo_salt", salt)
        _config_set(con, "codigo_falhas", "0")
    with open(ARQ_CODIGO_INICIAL, "w", encoding="utf-8") as arq:
        arq.write("CODIGO INICIAL DO MINISTRO (uso unico)\n\n%s\n\n"
                  "Digite este codigo na tela de configuracao inicial.\n"
                  "O arquivo e apagado automaticamente apos o uso.\n" % codigo)


def garantir_codigo_inicial():
    """Se ja existe Ministro, apaga restos do codigo e retorna False.
    Senao garante um codigo valido (arquivo e banco coerentes) e retorna True."""
    if existe_ministro():
        concluir_codigo_inicial()
        return False
    with banco() as con:
        tem_hash = _config_get(con, "codigo_hash") is not None
    if not tem_hash or not os.path.isfile(ARQ_CODIGO_INICIAL) or not _arquivo_codigo_confere():
        gerar_codigo_inicial()
    return True


def validar_codigo_inicial(codigo):
    """True se o codigo confere. Apos MAX_FALHAS_CODIGO erros, o codigo e trocado por outro."""
    if _codigo_bate(codigo):
        return True
    with banco() as con:
        if _config_get(con, "codigo_hash") is None:
            return False
        try:
            falhas = int(_config_get(con, "codigo_falhas") or 0) + 1
        except ValueError:
            falhas = 1
        _config_set(con, "codigo_falhas", str(falhas))
    if falhas >= MAX_FALHAS_CODIGO:
        gerar_codigo_inicial()
        registrar_evento("(configuracao)",
                         "Codigo inicial renovado apos %d erros" % MAX_FALHAS_CODIGO)
    return False


def concluir_codigo_inicial():
    try:
        with banco() as con:
            con.execute("DELETE FROM configuracao WHERE chave IN "
                        "('codigo_hash', 'codigo_salt', 'codigo_falhas')")
    except sqlite3.Error:
        pass
    try:
        os.remove(ARQ_CODIGO_INICIAL)
    except OSError:
        pass


# =========================================================
# CADASTRO / ADMINISTRACAO (todas exigem o nivel dentro da propria funcao)
# =========================================================
def _validar_senha_nova(senha, confirmacao=None):
    if not senha or len(senha) < 8:
        raise ValueError("A senha precisa ter pelo menos 8 caracteres.")
    if confirmacao is not None and senha != confirmacao:
        raise ValueError("A confirmacao de senha nao confere.")


def _validar_dados(nome, usuario, senha, confirmacao=None):
    nome = (nome or "").strip()
    usuario = (usuario or "").strip().lower()
    if not nome or not usuario or not senha:
        raise ValueError("Preencha todos os campos.")
    if len(nome) > 100:
        raise ValueError("Nome muito longo (maximo 100 caracteres).")
    if not REGEX_USUARIO_NOVO.match(usuario):
        raise ValueError("Usuario invalido. Use 3 a 30 caracteres: letras minusculas, "
                         "numeros, _ ou -.")
    _validar_senha_nova(senha, confirmacao)
    if buscar_funcionario(usuario) is not None:
        raise ValueError("Este usuario ja existe.")
    return nome, usuario


def _validar_amostras(amostras):
    if amostras is None or len(amostras) < AMOSTRAS_CADASTRO:
        raise ValueError("Cadastro facial incompleto.")


def _remover_usuario_db(usuario):
    with banco() as con:
        con.execute("DELETE FROM funcionarios WHERE usuario = ?", (usuario,))


def _limpar_temporario(usuario):
    try:
        os.remove(arquivo_rosto(usuario)[:-4] + ".tmp.npz")
    except (OSError, ValueError):
        pass


def cadastrar_ministro_inicial(codigo, nome, usuario, senha, confirmacao, amostras):
    """Unico caminho para criar um Ministro. Exige o codigo inicial e nenhum Ministro ativo."""
    if existe_ministro():
        raise PermissionError("O Ministro ja foi configurado.")
    if not validar_codigo_inicial(codigo):
        registrar_evento("(configuracao)", "Codigo inicial incorreto")
        raise PermissionError("Codigo inicial incorreto.")
    nome, usuario = _validar_dados(nome, usuario, senha, confirmacao)
    _validar_amostras(amostras)
    try:
        with banco() as con:
            h, salt = gerar_hash(senha)
            cursor = con.execute(
                "INSERT INTO funcionarios (nome, usuario, senha_hash, salt, nivel, iteracoes) "
                "SELECT ?, ?, ?, ?, 3, ? WHERE NOT EXISTS "
                "(SELECT 1 FROM funcionarios WHERE nivel = 3 AND ativo = 1)",
                (nome, usuario, h, salt, ITER_ATUAL))
            if cursor.rowcount == 0:
                raise PermissionError("O Ministro ja foi configurado.")
    except sqlite3.IntegrityError:
        raise ValueError("Este usuario ja existe.")
    try:
        salvar_amostras(usuario, amostras)
    except Exception as erro:
        _remover_usuario_db(usuario)
        _limpar_temporario(usuario)
        raise RuntimeError("Nao foi possivel salvar o rosto: %s" % erro)
    concluir_codigo_inicial()
    registrar_evento(usuario, "Ministro configurado (primeiro acesso)")


def cadastrar_funcionario(ator_usuario, nome, usuario, senha, confirmacao, nivel, amostras):
    ator = exigir_nivel(ator_usuario, 3, "cadastrar funcionario")
    if nivel not in (1, 2):
        raise ValueError("O Ministro so pode cadastrar funcionarios de nivel 1 ou 2.")
    nome, usuario = _validar_dados(nome, usuario, senha, confirmacao)
    _validar_amostras(amostras)
    try:
        with banco() as con:
            h, salt = gerar_hash(senha)
            con.execute("INSERT INTO funcionarios (nome, usuario, senha_hash, salt, nivel, iteracoes) "
                        "VALUES (?, ?, ?, ?, ?, ?)", (nome, usuario, h, salt, nivel, ITER_ATUAL))
    except sqlite3.IntegrityError:
        raise ValueError("Este usuario ja existe.")
    try:
        salvar_amostras(usuario, amostras)
    except Exception as erro:
        _remover_usuario_db(usuario)
        _limpar_temporario(usuario)
        raise RuntimeError("Nao foi possivel salvar o rosto: %s" % erro)
    registrar_evento(ator["usuario"], "Cadastrou %s (nivel %d)" % (usuario, nivel))


def remover_funcionario(ator_usuario, usuario):
    ator = exigir_nivel(ator_usuario, 3, "remover funcionario")
    alvo = buscar_funcionario(usuario)
    if alvo is None:
        raise ValueError("Funcionario nao encontrado.")
    if alvo["id"] == ator["id"]:
        raise ValueError("Voce nao pode remover a propria conta.")
    if alvo["nivel"] == 3:
        with banco() as con:
            ministros = con.execute("SELECT COUNT(*) FROM funcionarios WHERE nivel = 3 AND ativo = 1"
                                    ).fetchone()[0]
        if ministros <= 1:
            raise ValueError("O sistema nao pode ficar sem um Ministro.")
    _remover_usuario_db(alvo["usuario"])
    try:
        arquivar_rosto(alvo["usuario"], mover=True)  # nao apaga: guarda em rostos_arquivo
    except (OSError, ValueError):
        pass
    registrar_evento(ator["usuario"], "Removeu o funcionario " + alvo["usuario"])


def desbloquear_conta(ator_usuario, usuario):
    ator = exigir_nivel(ator_usuario, 3, "desbloquear conta")
    if buscar_funcionario(usuario) is None:
        raise ValueError("Funcionario nao encontrado.")
    zerar_falhas(usuario)
    registrar_evento(ator["usuario"], "Desbloqueou a conta " + usuario)


def alterar_nivel(ator_usuario, usuario, novo_nivel):
    ator = exigir_nivel(ator_usuario, 3, "alterar nivel")
    if novo_nivel not in (1, 2):
        raise ValueError("Somente os niveis 1 e 2 podem ser atribuidos.")
    alvo = buscar_funcionario(usuario)
    if alvo is None:
        raise ValueError("Funcionario nao encontrado.")
    if alvo["nivel"] == 3:
        raise ValueError("O nivel do Ministro nao pode ser alterado.")
    with banco() as con:
        con.execute("UPDATE funcionarios SET nivel = ? WHERE usuario = ?",
                    (novo_nivel, alvo["usuario"]))
    registrar_evento(ator["usuario"], "Alterou %s para nivel %d" % (alvo["usuario"], novo_nivel))


def redefinir_senha(ator_usuario, usuario, nova_senha, confirmacao=None):
    """Permite ao Ministro recuperar contas antigas sem credencial valida ou com senha esquecida."""
    ator = exigir_nivel(ator_usuario, 3, "redefinir senha")
    alvo = buscar_funcionario(usuario)
    if alvo is None:
        raise ValueError("Funcionario nao encontrado.")
    _validar_senha_nova(nova_senha, confirmacao)
    h, salt = gerar_hash(nova_senha)
    with banco() as con:
        con.execute("UPDATE funcionarios SET senha_hash=?, salt=?, iteracoes=?, falhas=0, "
                    "bloqueado_ate=NULL WHERE usuario=?", (h, salt, ITER_ATUAL, alvo["usuario"]))
    registrar_evento(ator["usuario"], "Redefiniu a senha de " + alvo["usuario"])


def substituir_rosto(ator_usuario, usuario, amostras):
    ator = exigir_nivel(ator_usuario, 3, "recadastrar rosto")
    alvo = buscar_funcionario(usuario)
    if alvo is None:
        raise ValueError("Funcionario nao encontrado.")
    _validar_amostras(amostras)
    salvar_amostras(alvo["usuario"], amostras)  # o rosto anterior e arquivado antes
    registrar_evento(ator["usuario"], "Recadastrou o rosto de " + alvo["usuario"])


def listar_funcionarios(ator_usuario):
    exigir_nivel(ator_usuario, 2, "consultar funcionarios")
    with banco() as con:
        linhas = con.execute("SELECT * FROM funcionarios ORDER BY nivel DESC, nome").fetchall()
    resultado = []
    for l in linhas:
        resultado.append({
            "nome": l["nome"] or l["usuario"], "usuario": l["usuario"], "nivel": l["nivel"],
            "bloqueado": segundos_de_bloqueio(l) > 0,
            "sem_senha": not conta_tem_credencial(l),
            "rosto": status_rosto(l["usuario"]),
        })
    return resultado


def listar_registros(ator_usuario, limite=300):
    exigir_nivel(ator_usuario, 2, "consultar registros")
    with banco() as con:
        return con.execute("SELECT usuario, evento, data_hora FROM registros "
                           "ORDER BY id DESC LIMIT ?", (int(limite),)).fetchall()


# =========================================================
# LOGIN (senha) - logica separada da interface
# =========================================================
def validar_usuario_e_senha(login, senha):
    """Retorna (status, funcionario, mensagem). status: 'ok', 'negado' ou 'bloqueado'."""
    login = (login or "").strip().lower()
    func = buscar_funcionario(login)
    if func is None or not func["ativo"]:
        gerar_hash(senha or "")  # gasta o mesmo tempo, para nao revelar se o usuario existe
        registrar_evento("(desconhecido)", "Login invalido: usuario inexistente")
        return "negado", None, MSG_LOGIN_INVALIDO

    segundos = segundos_de_bloqueio(func)
    if segundos > 0:
        registrar_evento(func["usuario"], "Tentativa de login com conta bloqueada")
        minutos = int(math.ceil(segundos / 60.0))
        return "bloqueado", None, ("Conta temporariamente bloqueada por excesso de falhas.\n"
                                   "Tente novamente em ~%d min ou peca ao Ministro para desbloquear."
                                   % minutos)

    if not conta_tem_credencial(func):
        registrar_evento(func["usuario"], "Login negado: conta sem senha valida")
        return "negado", None, ("Esta conta nao possui senha valida.\n"
                                "Peca ao Ministro para redefinir a senha.")

    if not validar_senha(senha or "", func):
        bloqueou = registrar_falha(func["usuario"])
        registrar_evento(func["usuario"], "Falha de senha")
        mensagem = MSG_LOGIN_INVALIDO
        if bloqueou:
            registrar_evento(func["usuario"], "Conta bloqueada por %d min" % BLOQUEIO_MINUTOS)
            mensagem += "\nConta bloqueada por %d minutos." % BLOQUEIO_MINUTOS
        return "negado", None, mensagem
    return "ok", func, ""


def concluir_login(func, senha):
    zerar_falhas(func["usuario"])
    try:
        migrar_hash_se_preciso(func["usuario"], senha)
    except Exception:
        registrar_evento(func["usuario"], "Aviso: hash da senha nao foi atualizado")
    registrar_evento(func["usuario"], "Acesso autorizado")


def registrar_falha_facial(func):
    bloqueou = registrar_falha(func["usuario"])
    registrar_evento(func["usuario"], "Falha na verificacao facial")
    mensagem = "Nao foi possivel confirmar o rosto.\nTente novamente com boa iluminacao."
    if bloqueou:
        registrar_evento(func["usuario"], "Conta bloqueada por %d min" % BLOQUEIO_MINUTOS)
        mensagem += "\nConta bloqueada por %d minutos." % BLOQUEIO_MINUTOS
    return mensagem


# =========================================================
# PROCESSAMENTO DE IMAGEM (mesmo pipeline na captura e na verificacao)
# =========================================================
def carregar_detector():
    caminhos = [CASCADE_LOCAL]
    pasta_cv = getattr(getattr(cv2, "data", None), "haarcascades", None)
    if pasta_cv:
        caminhos.append(os.path.join(pasta_cv, "haarcascade_frontalface_default.xml"))
    for caminho in caminhos:
        if os.path.isfile(caminho):
            detector = cv2.CascadeClassifier(caminho)
            if not detector.empty():
                return detector
    raise FileNotFoundError(
        "Classificador haarcascade_frontalface_default.xml nao encontrado.\n"
        "Coloque o arquivo na mesma pasta do main.py.")


def abrir_camera():
    backends = (cv2.CAP_DSHOW, cv2.CAP_ANY) if os.name == "nt" else (cv2.CAP_ANY,)
    for indice in (0, 1, 2):
        for backend in backends:
            camera = cv2.VideoCapture(indice, backend)
            if camera.isOpened():
                ok, quadro = camera.read()
                if ok and quadro is not None:
                    return camera
            camera.release()
    raise RuntimeError("Webcam indisponivel. Conecte a camera, feche outros programas que a usam "
                       "e verifique as permissoes de privacidade do sistema.")


def detectar_rosto(quadro, detector):
    """
    Pipeline unico (captura e verificacao): cinza -> deteccao -> recorte -> 200x200 -> equalizacao.
    Retorna (rosto_processado, caixa, quantidade_de_rostos). Exige EXATAMENTE 1 rosto.
    """
    cinza = cv2.cvtColor(quadro, cv2.COLOR_BGR2GRAY)
    rostos = detector.detectMultiScale(cinza, scaleFactor=1.1, minNeighbors=6, minSize=(90, 90))
    if len(rostos) != 1:
        caixa = tuple(int(v) for v in rostos[0]) if len(rostos) else None
        return None, caixa, len(rostos)
    x, y, w, h = [int(v) for v in rostos[0]]
    recorte = cv2.resize(cinza[y:y + h, x:x + w], TAMANHO_ROSTO)
    return cv2.equalizeHist(recorte), (x, y, w, h), 1


def desenhar(quadro, caixa, texto, cor=(0, 255, 0)):
    if caixa is not None:
        x, y, w, h = caixa
        cv2.rectangle(quadro, (x, y), (x + w, y + h), cor, 2)
    cv2.putText(quadro, texto, (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 0.65, cor, 2)
    cv2.putText(quadro, "Q ou ESC para cancelar", (10, 60),
                cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 255, 255), 1)


# =========================================================
# AMOSTRAS FACIAIS (pasta rostos/) - compativel com as amostras antigas
# =========================================================
def arquivo_rosto(usuario):
    """Caminho do .npz do usuario. Aceita nomes do banco antigo (ex.: com acento), mas
    recusa qualquer nome que possa escapar da pasta rostos."""
    nome = (usuario or "").strip()
    proibidos = '\\/:*?"<>|\0'
    if (not nome or nome in (".", "..") or nome != os.path.basename(nome)
            or any(c in nome for c in proibidos)):
        raise ValueError("Nome de usuario invalido para arquivo facial.")
    return os.path.join(PASTA_ROSTOS, nome + ".npz")


def arquivar_rosto(usuario, mover=False):
    """Guarda uma copia (ou move) do arquivo facial para rostos_arquivo, sem sobrescrever nada."""
    origem = arquivo_rosto(usuario)
    if not os.path.isfile(origem):
        return None
    os.makedirs(PASTA_ARQUIVO, exist_ok=True)
    carimbo = datetime.now().strftime("%Y%m%d_%H%M%S")
    destino = os.path.join(PASTA_ARQUIVO, "%s_%s.npz" % (usuario, carimbo))
    contador = 1
    while os.path.exists(destino):
        destino = os.path.join(PASTA_ARQUIVO, "%s_%s_%d.npz" % (usuario, carimbo, contador))
        contador += 1
    (shutil.move if mover else shutil.copy2)(origem, destino)
    return destino


def salvar_amostras(usuario, amostras):
    """Grava em arquivo temporario; arquiva o rosto anterior (se houver) e so entao troca."""
    os.makedirs(PASTA_ROSTOS, exist_ok=True)
    destino = arquivo_rosto(usuario)
    temporario = destino[:-4] + ".tmp.npz"
    np.savez_compressed(temporario, imagens=np.array(amostras, dtype=np.uint8))
    if os.path.isfile(destino):
        arquivar_rosto(usuario, mover=False)
    os.replace(temporario, destino)


def ler_amostras(usuario):
    """Retorna lista de imagens 200x200. Levanta FileNotFoundError ou ValueError (corrompido)."""
    caminho = arquivo_rosto(usuario)
    if not os.path.isfile(caminho):
        raise FileNotFoundError("Este usuario nao possui rosto cadastrado.")
    try:
        with np.load(caminho, allow_pickle=False) as dados:
            imagens = dados["imagens"]
        if imagens.ndim != 3 or len(imagens) == 0:
            raise ValueError("formato inesperado")
        return [cv2.resize(i.astype(np.uint8), TAMANHO_ROSTO) for i in imagens]
    except Exception:
        raise ValueError("O arquivo facial deste usuario esta corrompido. "
                         "Peca ao Ministro para recadastrar o rosto.")


def status_rosto(usuario):
    try:
        ler_amostras(usuario)
        return "OK"
    except FileNotFoundError:
        return "Sem rosto"
    except ValueError:
        return "Corrompido"


def capturar_amostras(titulo="Cadastro facial"):
    """Abre a webcam e coleta AMOSTRAS_CADASTRO recortes. Retorna a lista, ou None se cancelado
    (ou se o tempo maximo acabar)."""
    detector = carregar_detector()
    camera = abrir_camera()
    amostras, contador = [], 0
    try:
        while len(amostras) < AMOSTRAS_CADASTRO:
            contador += 1
            if contador > QUADROS_MAX_CADASTRO:
                return None
            ok, quadro = camera.read()
            if not ok or quadro is None:
                raise RuntimeError("Erro ao capturar imagem da webcam.")
            quadro = cv2.flip(quadro, 1)
            rosto, caixa, quantidade = detectar_rosto(quadro, detector)
            if rosto is not None:
                if contador % 4 == 0:  # espaca as fotos para variar pose e expressao
                    amostras.append(rosto)
                desenhar(quadro, caixa, "Amostras: %d/%d" % (len(amostras), AMOSTRAS_CADASTRO))
            else:
                mensagem = "Nenhum rosto" if quantidade == 0 else "Apenas 1 pessoa na camera"
                desenhar(quadro, caixa, mensagem, (0, 200, 255))
            cv2.imshow(titulo, quadro)
            if cv2.waitKey(1) & 0xFF in (ord("q"), 27):
                return None
    finally:
        camera.release()
        cv2.destroyAllWindows()
    return amostras


# =========================================================
# RECONHECIMENTO FACIAL (LBPH)
# =========================================================
def criar_reconhecedor():
    if not (hasattr(cv2, "face") and hasattr(cv2.face, "LBPHFaceRecognizer_create")):
        raise RuntimeError("O modulo cv2.face nao esta instalado. No terminal rode:\n"
                           "pip uninstall -y opencv-python opencv-python-headless\n"
                           "pip install opencv-contrib-python")
    return cv2.face.LBPHFaceRecognizer_create(radius=1, neighbors=8, grid_x=8, grid_y=8)


def treinar_modelo():
    """Treina com os rostos de TODOS os funcionarios ativos (rotulo = id), para que um
    rosto parecido com o de OUTRA pessoa cadastrada seja identificado como ela e recusado."""
    imagens, rotulos = [], []
    with banco() as con:
        lista = con.execute("SELECT id, usuario FROM funcionarios WHERE ativo = 1").fetchall()
    for func in lista:
        try:
            for imagem in ler_amostras(func["usuario"]):
                imagens.append(imagem)
                rotulos.append(func["id"])
        except (FileNotFoundError, ValueError):
            continue  # sem rosto ou corrompido: fica de fora do modelo
    if not imagens:
        raise RuntimeError("Nenhum rosto cadastrado para treinar o reconhecimento.")
    reconhecedor = criar_reconhecedor()
    reconhecedor.train(imagens, np.array(rotulos, dtype=np.int32))
    return reconhecedor


def avaliar_rosto(reconhecedor, rosto, id_esperado):
    """Verificacao 1:1. Aprova somente se o modelo apontar o PROPRIO usuario e a distancia
    LBPH for menor que o limiar. A distancia NAO e uma probabilidade de identidade."""
    rotulo, distancia = reconhecedor.predict(rosto)
    return (rotulo == id_esperado and distancia <= LIMIAR_LBPH), distancia


def verificar_rosto(func):
    """
    Retorna 'ok', 'falhou', 'sem_rosto' ou 'cancelado'. Somente 'ok' concede acesso.
    'ok' exige QUADROS_APROVACAO quadros SEGUIDOS confirmando o usuario; qualquer quadro
    sem rosto, com 2+ pessoas ou com rosto diferente zera a sequencia.
    Problemas tecnicos (camera, classificador, arquivo facial) levantam excecao.
    """
    ler_amostras(func["usuario"])  # levanta erro claro se ausente ou corrompido
    reconhecedor = treinar_modelo()
    detector = carregar_detector()
    camera = abrir_camera()
    seguidos = 0
    viu_rosto = False
    try:
        for _ in range(QUADROS_MAXIMOS):
            ok, quadro = camera.read()
            if not ok or quadro is None:
                raise RuntimeError("Falha ao ler imagens da webcam durante a verificacao.")
            quadro = cv2.flip(quadro, 1)
            rosto, caixa, quantidade = detectar_rosto(quadro, detector)
            if rosto is None:
                seguidos = 0
                mensagem = "Procurando rosto..." if quantidade == 0 else "Apenas 1 pessoa por vez"
                desenhar(quadro, caixa, mensagem, (0, 200, 255))
            else:
                viu_rosto = True
                aprovado, distancia = avaliar_rosto(reconhecedor, rosto, func["id"])
                if DEBUG:
                    print("[DEBUG] distancia LBPH = %.1f (limiar %.1f)" % (distancia, LIMIAR_LBPH))
                seguidos = seguidos + 1 if aprovado else 0
                desenhar(quadro, caixa,
                         "%s (%d/%d)" % ("Validando" if aprovado else "Nao confere",
                                         seguidos, QUADROS_APROVACAO),
                         (0, 255, 0) if aprovado else (0, 0, 255))
            cv2.imshow("Verificacao facial", quadro)
            if cv2.waitKey(1) & 0xFF in (ord("q"), 27):
                return "cancelado"
            if seguidos >= QUADROS_APROVACAO:
                return "ok"
    finally:
        camera.release()
        cv2.destroyAllWindows()
    return "falhou" if viu_rosto else "sem_rosto"


# =========================================================
# TEMA VISUAL (somente aparencia: nenhuma regra de negocio fica aqui)
# =========================================================
COR_NAVY = "#0B1F3A"          # cabecalho azul-marinho
COR_NAVY_CLARO = "#16315C"
COR_AZUL = "#1D4ED8"          # botoes principais
COR_AZUL_HOVER = "#2563EB"
COR_AZUL_PRESS = "#1E40AF"
COR_FUNDO = "#E9EEF6"
COR_CARTAO = "#FFFFFF"
COR_BORDA = "#C9D4E5"
COR_TEXTO = "#1F2937"
COR_MUDO = "#6B7280"
COR_ERRO = "#B00020"
COR_OK = "#1B5E20"
COR_AVISO = "#B26A00"

FONTE = "Segoe UI"
F_TEXTO = (FONTE, 11)
F_NEGRITO = (FONTE, 11, "bold")
F_TITULO = (FONTE, 22, "bold")
F_SUBTITULO = (FONTE, 11)
F_SECAO = (FONTE, 13, "bold")
F_PEQUENO = (FONTE, 9)


# =========================================================
# INTERFACE GRAFICA
# =========================================================
class Aplicacao:
    def __init__(self, janela):
        self.janela = janela
        self.sessao = None  # {"usuario", "nome", "nivel"} enquanto houver login
        self.janela.title("Sistema Biometrico - APS")
        self.configurar_janela()
        self.aplicar_tema()
        self.tela_inicial()

    # ---------- janela e tema ----------
    def configurar_janela(self):
        """Janela grande, centralizada e que cabe em telas pequenas."""
        try:
            tela_l = int(self.janela.winfo_screenwidth())
            tela_a = int(self.janela.winfo_screenheight())
            largura = min(1100, tela_l - 60)
            altura = min(800, tela_a - 100)
            x = max(0, (tela_l - largura) // 2)
            y = max(0, (tela_a - altura) // 2 - 20)
            self.janela.geometry("%dx%d+%d+%d" % (largura, altura, x, y))
        except (tk.TclError, TypeError, ValueError):
            self.janela.geometry("1100x760")
        self.janela.minsize(860, 600)

    def aplicar_tema(self):
        estilo = ttk.Style()
        try:
            estilo.theme_use("clam")
        except tk.TclError:
            pass
        self.janela.configure(bg=COR_FUNDO)
        self.janela.option_add("*TCombobox*Listbox.font", F_TEXTO)

        estilo.configure(".", font=F_TEXTO, background=COR_CARTAO, foreground=COR_TEXTO)
        estilo.configure("TFrame", background=COR_CARTAO)
        estilo.configure("Card.TFrame", background=COR_CARTAO, borderwidth=1, relief="solid",
                         bordercolor=COR_BORDA)
        estilo.configure("Header.TFrame", background=COR_NAVY)

        estilo.configure("TLabel", background=COR_CARTAO, foreground=COR_TEXTO, font=F_TEXTO)
        estilo.configure("HeaderTitulo.TLabel", background=COR_NAVY, foreground="#FFFFFF",
                         font=F_TITULO)
        estilo.configure("HeaderSub.TLabel", background=COR_NAVY, foreground="#BFD0EA",
                         font=F_SUBTITULO)
        estilo.configure("Secao.TLabel", foreground=COR_NAVY, font=F_SECAO)
        estilo.configure("Mudo.TLabel", foreground=COR_MUDO, font=F_TEXTO)
        estilo.configure("Erro.TLabel", foreground=COR_ERRO, font=F_NEGRITO)
        estilo.configure("Rodape.TLabel", background=COR_FUNDO, foreground=COR_MUDO,
                         font=F_PEQUENO)

        # Botoes: Primary (azul), Sec (branco com borda) e Danger (vermelho)
        modelos = [
            ("Primary", COR_AZUL, COR_AZUL_HOVER, COR_AZUL_PRESS, "#FFFFFF", COR_AZUL),
            ("Sec", "#FFFFFF", "#EEF3FB", "#DCE6F7", COR_NAVY, COR_BORDA),
            ("Danger", "#C62828", "#D32F2F", "#B71C1C", "#FFFFFF", "#C62828"),
        ]
        for nome, normal, hover, pressionado, texto, borda in modelos:
            estilo.configure(nome + ".TButton", background=normal, foreground=texto,
                             bordercolor=borda, lightcolor=normal, darkcolor=normal,
                             focuscolor=normal, borderwidth=1, relief="flat",
                             padding=(18, 10), font=F_NEGRITO)
            estilo.map(nome + ".TButton",
                       background=[("pressed", pressionado), ("active", hover)],
                       bordercolor=[("pressed", pressionado), ("active", hover)],
                       lightcolor=[("pressed", pressionado), ("active", hover)],
                       darkcolor=[("pressed", pressionado), ("active", hover)],
                       foreground=[("disabled", "#9AA5B8")])
        estilo.configure("TButton", background="#FFFFFF", foreground=COR_NAVY,
                         bordercolor=COR_BORDA, padding=(18, 10), font=F_NEGRITO)

        # Campos de texto
        estilo.configure("TEntry", fieldbackground="#FFFFFF", foreground=COR_TEXTO,
                         bordercolor=COR_BORDA, lightcolor=COR_BORDA, darkcolor=COR_BORDA,
                         padding=(10, 7), insertcolor=COR_TEXTO)
        estilo.map("TEntry", bordercolor=[("focus", COR_AZUL)], lightcolor=[("focus", COR_AZUL)],
                   darkcolor=[("focus", COR_AZUL)])
        estilo.configure("TCombobox", fieldbackground="#FFFFFF", background="#FFFFFF",
                         foreground=COR_TEXTO, bordercolor=COR_BORDA, lightcolor=COR_BORDA,
                         darkcolor=COR_BORDA, arrowcolor=COR_NAVY, padding=(10, 7))
        estilo.map("TCombobox", fieldbackground=[("readonly", "#FFFFFF")],
                   bordercolor=[("focus", COR_AZUL)], lightcolor=[("focus", COR_AZUL)],
                   darkcolor=[("focus", COR_AZUL)])

        # Tabelas
        estilo.configure("Treeview", background="#FFFFFF", fieldbackground="#FFFFFF",
                         foreground=COR_TEXTO, rowheight=32, borderwidth=0, font=F_TEXTO)
        estilo.configure("Treeview.Heading", background=COR_NAVY, foreground="#FFFFFF",
                         font=F_NEGRITO, relief="flat", borderwidth=0, padding=(10, 8))
        estilo.map("Treeview.Heading", background=[("active", COR_NAVY_CLARO)])
        estilo.map("Treeview", background=[("selected", COR_AZUL)],
                   foreground=[("selected", "#FFFFFF")])
        estilo.configure("Vertical.TScrollbar", background="#C9D4E5", troughcolor="#EEF3FB",
                         bordercolor="#EEF3FB", arrowcolor=COR_NAVY)

    # ---------- componentes visuais reutilizaveis ----------
    def limpar(self):
        for item in self.janela.winfo_children():
            item.destroy()

    def titulo(self, texto, subtitulo=""):
        """Cabecalho azul-marinho, faixa de destaque e rodape da janela."""
        cabecalho = ttk.Frame(self.janela, style="Header.TFrame", padding=(40, 20))
        cabecalho.pack(fill="x")
        ttk.Label(cabecalho, text=texto, style="HeaderTitulo.TLabel").pack(anchor="w")
        if subtitulo:
            ttk.Label(cabecalho, text=subtitulo, style="HeaderSub.TLabel").pack(
                anchor="w", pady=(4, 0))
        tk.Frame(self.janela, bg=COR_AZUL, height=3).pack(fill="x")
        ttk.Label(self.janela, style="Rodape.TLabel",
                  text="Projeto academico APS  |  Solucao didatica, sem prova de vida"
                  ).pack(side="bottom", pady=(0, 8))

    def cartao(self, lateral=170, expandir=True):
        """Cartao branco centralizado onde fica o conteudo de cada tela."""
        carta = ttk.Frame(self.janela, style="Card.TFrame", padding=26)
        carta.pack(fill="both" if expandir else "x", expand=expandir, padx=lateral,
                   pady=(20, 14))
        return carta

    def botao(self, pai, texto, comando, estilo="Primary.TButton"):
        ttk.Button(pai, text=texto, command=comando, style=estilo).pack(fill="x", pady=5)

    def linha_botoes(self, pai, itens):
        """Botoes lado a lado. itens = [(texto, comando, estilo), ...]"""
        linha = ttk.Frame(pai)
        linha.pack(fill="x", pady=(14, 0))
        for posicao, (texto, comando, estilo) in enumerate(itens):
            ttk.Button(linha, text=texto, command=comando, style=estilo).pack(
                side="left", expand=True, fill="x", padx=(0 if posicao == 0 else 8, 0))

    def grade_botoes(self, pai, itens, colunas=2):
        """Botoes em grade. itens = [(texto, comando, estilo), ...]"""
        quadro = ttk.Frame(pai)
        quadro.pack(fill="x", pady=(8, 0))
        for c in range(colunas):
            quadro.columnconfigure(c, weight=1, uniform="botoes")
        for posicao, (texto, comando, estilo) in enumerate(itens):
            ttk.Button(quadro, text=texto, command=comando, style=estilo).grid(
                row=posicao // colunas, column=posicao % colunas, sticky="ew", padx=4, pady=4)

    def campo(self, pai, texto, segredo=False):
        ttk.Label(pai, text=texto).pack(anchor="w", pady=(8, 3))
        entrada = ttk.Entry(pai, show="*" if segredo else "", font=F_TEXTO)
        entrada.pack(fill="x")
        return entrada

    def campo_em(self, grade, texto, linha, coluna, segredo=False, colunas=1):
        """Campo posicionado em uma grade (formularios em duas colunas)."""
        quadro = ttk.Frame(grade)
        quadro.grid(row=linha, column=coluna, columnspan=colunas, sticky="ew",
                    padx=(0 if coluna == 0 else 12, 0), pady=(0, 8))
        ttk.Label(quadro, text=texto).pack(anchor="w", pady=(0, 3))
        entrada = ttk.Entry(quadro, show="*" if segredo else "", font=F_TEXTO)
        entrada.pack(fill="x")
        return entrada

    def nova_grade(self, pai):
        grade = ttk.Frame(pai)
        grade.pack(fill="x")
        grade.columnconfigure(0, weight=1)
        grade.columnconfigure(1, weight=1)
        return grade

    def criar_tabela(self, pai, colunas):
        """Tabela com cabecalho azul-marinho, linhas alternadas e barra de rolagem.
        colunas = [(chave, titulo, largura, alinhamento), ...]"""
        area = ttk.Frame(pai)
        area.pack(fill="both", expand=True)
        tabela = ttk.Treeview(area, columns=[c[0] for c in colunas], show="headings",
                              selectmode="browse")
        rolagem = ttk.Scrollbar(area, orient="vertical", command=tabela.yview)
        tabela.configure(yscrollcommand=rolagem.set)
        for chave, texto, largura, alinhamento in colunas:
            tabela.heading(chave, text=texto, anchor=alinhamento)
            tabela.column(chave, width=largura, minwidth=70, anchor=alinhamento, stretch=True)
        tabela.tag_configure("par", background="#FFFFFF")
        tabela.tag_configure("impar", background="#F1F5FB")
        tabela.tag_configure("alerta", foreground=COR_ERRO)
        tabela.tag_configure("aviso", foreground=COR_AVISO)
        tabela.tag_configure("ok", foreground=COR_OK)
        tabela.pack(side="left", fill="both", expand=True)
        rolagem.pack(side="right", fill="y")
        return tabela

    # ---------- mensagens (sempre trazidas para a frente da janela) ----------
    def trazer_frente(self):
        try:
            self.janela.update_idletasks()
            self.janela.lift()
            self.janela.attributes("-topmost", True)
            self.janela.after(300, lambda: self.janela.attributes("-topmost", False))
            self.janela.focus_force()
        except tk.TclError:
            pass

    def erro(self, titulo, mensagem):
        self.trazer_frente()
        messagebox.showerror(titulo, mensagem, parent=self.janela)

    def aviso(self, titulo, mensagem):
        self.trazer_frente()
        messagebox.showwarning(titulo, mensagem, parent=self.janela)

    def info(self, titulo, mensagem):
        self.trazer_frente()
        messagebox.showinfo(titulo, mensagem, parent=self.janela)

    def confirmar(self, titulo, mensagem):
        self.trazer_frente()
        return messagebox.askyesno(titulo, mensagem, parent=self.janela)

    # ---------- sessao e erros ----------
    def usuario_atual(self):
        return self.sessao["usuario"] if self.sessao else None

    def exigir_sessao(self, nivel_minimo=1):
        """Guarda de tela: reconsulta o nivel no banco; sem sessao valida volta ao inicio.
        (As funcoes administrativas revalidam de novo por conta propria.)"""
        if self.sessao:
            try:
                self.sessao["nivel"] = obter_ator(self.sessao["usuario"])["nivel"]
            except (PermissionError, sqlite3.Error):
                self.sessao = None
                self.erro("Sessao invalida", "Sua sessao nao e mais valida. Entre novamente.")
        if not self.sessao or self.sessao["nivel"] < nivel_minimo:
            if self.sessao:
                registrar_evento(self.sessao["usuario"], "ACESSO NEGADO: tela restrita")
                self.erro("Acesso negado", "Voce nao tem permissao para esta area.")
            self.sessao = None
            self.tela_inicial()
            return False
        return True

    def tratar_erro(self, erro):
        if isinstance(erro, PermissionError):
            self.erro("Acesso negado", str(erro))
        elif isinstance(erro, ValueError):
            self.erro("Dados invalidos", str(erro))
        elif isinstance(erro, sqlite3.Error):
            self.erro("Banco de dados", "Erro no banco de dados: %s" % erro)
        else:
            self.erro("Erro", str(erro))

    # ---------- tela inicial ----------
    def tela_inicial(self):
        self.sessao = None
        self.limpar()
        self.titulo("Sistema de Autenticacao Biometrica",
                    "Ministerio do Meio Ambiente  |  Projeto academico APS")
        carta = self.cartao(lateral=190)
        ttk.Label(carta, text="Bem-vindo", style="Secao.TLabel").pack(anchor="w")
        ttk.Label(carta, style="Mudo.TLabel", wraplength=620, justify="left",
                  text="Cofre protegido por senha e reconhecimento facial, "
                       "com tres niveis de acesso.").pack(anchor="w", pady=(4, 18))
        try:
            sem_ministro = not existe_ministro()
            ha_usuarios = total_funcionarios() > 0
        except sqlite3.Error as erro:
            self.erro("Banco de dados", "Nao foi possivel ler o banco: %s" % erro)
            sem_ministro, ha_usuarios = False, False
        if sem_ministro:
            ttk.Label(carta, style="Erro.TLabel", wraplength=620, justify="left",
                      text="Configuracao inicial pendente: o Ministro ainda nao foi cadastrado. "
                           "E necessario o codigo de uso unico gerado na pasta do projeto."
                      ).pack(anchor="w", pady=(0, 10))
            self.botao(carta, "Configurar o Ministro (primeiro acesso)",
                       self.tela_configuracao_inicial)
        if ha_usuarios:
            self.botao(carta, "Entrar no sistema", self.tela_login)
        self.botao(carta, "Sobre o projeto", self.tela_sobre, "Sec.TButton")

    # ---------- configuracao inicial do Ministro ----------
    def tela_configuracao_inicial(self):
        try:
            if not garantir_codigo_inicial():
                self.tela_inicial()
                return
        except (OSError, sqlite3.Error) as erro:
            self.erro("Erro", "Nao foi possivel gerar o codigo inicial: %s" % erro)
            return
        self.limpar()
        self.titulo("Configuracao inicial do Ministro",
                    "Primeiro acesso: cria a conta de administracao do sistema")
        carta = self.cartao(lateral=110, expandir=False)
        ttk.Label(carta, style="Mudo.TLabel", wraplength=760, justify="left",
                  text="Abra o arquivo 'codigo_inicial_ministro.txt' na pasta do projeto, "
                       "copie o codigo e digite abaixo. O codigo vale uma unica vez e e "
                       "trocado apos %d erros." % MAX_FALHAS_CODIGO).pack(anchor="w", pady=(0, 12))
        grade = self.nova_grade(carta)
        c_codigo = self.campo_em(grade, "Codigo inicial:", 0, 0, colunas=2)
        c_nome = self.campo_em(grade, "Nome completo do Ministro:", 1, 0)
        c_usuario = self.campo_em(grade, "Usuario (3 a 30 caracteres):", 1, 1)
        c_senha = self.campo_em(grade, "Senha (minimo 8 caracteres):", 2, 0, segredo=True)
        c_conf = self.campo_em(grade, "Confirmar senha:", 2, 1, segredo=True)
        ttk.Label(carta, style="Mudo.TLabel", wraplength=760, justify="left",
                  text="Usuario: letras minusculas, numeros, _ ou -.").pack(anchor="w")

        def salvar():
            try:
                nome, usuario = _validar_dados(c_nome.get(), c_usuario.get(),
                                               c_senha.get(), c_conf.get())
                if not validar_codigo_inicial(c_codigo.get()):
                    registrar_evento("(configuracao)", "Codigo inicial incorreto")
                    raise PermissionError("Codigo inicial incorreto.")
                self.info("Cadastro facial",
                          "Agora vamos cadastrar o rosto do Ministro.\n"
                          "Olhe para a camera e mexa levemente a cabeca.")
                amostras = capturar_amostras("Cadastro facial do Ministro")
                if amostras is None:
                    self.aviso("Cancelado", "Cadastro facial cancelado ou nao concluido. "
                               "Nada foi salvo.")
                    return
                cadastrar_ministro_inicial(c_codigo.get(), nome, usuario, c_senha.get(),
                                           c_conf.get(), amostras)
                self.info("Sucesso", "Ministro cadastrado! Ja e possivel entrar.")
                self.tela_inicial()
            except Exception as erro:
                self.tratar_erro(erro)

        self.linha_botoes(carta, [("Voltar", self.tela_inicial, "Sec.TButton"),
                                  ("Salvar e cadastrar rosto", salvar, "Primary.TButton")])

    # ---------- login ----------
    def tela_login(self):
        self.sessao = None
        self.limpar()
        self.titulo("Login e autenticacao facial",
                    "Informe usuario e senha. Em seguida o rosto sera verificado pela webcam.")
        carta = self.cartao(lateral=230, expandir=False)
        c_usuario = self.campo(carta, "Usuario:")
        c_senha = self.campo(carta, "Senha:", True)
        estado = ttk.Label(carta, text="", style="Erro.TLabel", wraplength=520, justify="left")
        estado.pack(anchor="w", pady=(12, 2))

        def avisar(titulo, mensagem, tipo="erro"):
            """Mostra o aviso na propria tela (sempre visivel) e tambem em popup."""
            estado.config(text=mensagem, foreground=COR_OK if tipo == "info" else COR_ERRO)
            {"erro": self.erro, "aviso": self.aviso, "info": self.info}[tipo](titulo, mensagem)

        def entrar(evento=None):
            estado.config(text="")
            login = c_usuario.get().strip().lower()
            senha = c_senha.get()
            if not login or not senha:
                avisar("Campos obrigatorios", "Informe o usuario e a senha.", "aviso")
                return
            try:
                status, func, mensagem = validar_usuario_e_senha(login, senha)
                if status != "ok":
                    avisar("Acesso negado" if status == "negado" else "Conta bloqueada", mensagem)
                    c_senha.delete(0, "end")
                    return
                avisar("Verificacao facial", "Senha validada. Agora olhe para a webcam.", "info")
                resultado = verificar_rosto(func)
                if resultado == "ok":
                    concluir_login(func, senha)
                    self.sessao = {"usuario": func["usuario"], "nome": func["nome"] or func["usuario"],
                                   "nivel": func["nivel"]}
                    avisar("Acesso autorizado",
                           "Bem-vindo(a), %s!\nNivel %d: %s"
                           % (self.sessao["nome"], func["nivel"], NIVEIS[func["nivel"]]), "info")
                    self.tela_painel()
                    return
                if resultado == "cancelado":
                    registrar_evento(func["usuario"], "Verificacao facial cancelada")
                    avisar("Cancelado", "Verificacao cancelada. Nenhuma falha foi registrada.",
                           "info")
                elif resultado == "sem_rosto":
                    registrar_evento(func["usuario"], "Verificacao facial sem rosto detectado")
                    avisar("Nenhum rosto detectado",
                           "Nenhum rosto foi detectado pela camera.\n"
                           "Nenhuma falha foi registrada. Tente novamente.", "aviso")
                else:
                    avisar("Acesso negado", registrar_falha_facial(func))
                c_senha.delete(0, "end")
            except (FileNotFoundError, ValueError, RuntimeError) as erro:
                # Problema tecnico (camera, classificador, rosto ausente/corrompido): sem acesso.
                avisar("Nao foi possivel autenticar", str(erro))
            except Exception as erro:
                avisar("Erro", "Ocorreu um erro: %s" % erro)

        c_senha.bind("<Return>", entrar)
        c_usuario.focus_set()
        self.botao(carta, "Validar senha e rosto", entrar)
        self.botao(carta, "Voltar", self.tela_inicial, "Sec.TButton")

    # ---------- painel principal (por nivel) ----------
    def tela_painel(self):
        if not self.exigir_sessao(1):
            return
        nivel = self.sessao["nivel"]
        self.limpar()
        self.titulo("Painel de acesso autorizado",
                    "%s  |  Nivel %d - %s" % (self.sessao["nome"], nivel, NIVEIS[nivel]))
        carta = self.cartao(lateral=170)
        ttk.Label(carta, text="Permissoes deste nivel", style="Secao.TLabel").pack(
            anchor="w", pady=(0, 6))
        for permissao in PERMISSOES[nivel]:
            ttk.Label(carta, text="\u2022  " + permissao).pack(anchor="w", pady=1)
        if nivel == 3:
            ttk.Label(carta, text="PAINEL EXCLUSIVO DO MINISTRO",
                      style="Secao.TLabel").pack(anchor="w", pady=(12, 0))

        itens = [("Informacoes gerais", self.tela_info_geral, "Primary.TButton")]
        if nivel >= 2:
            itens.append(("Consultar funcionarios", self.tela_funcionarios, "Primary.TButton"))
            itens.append(("Consultar registros de acesso", self.tela_registros, "Primary.TButton"))
        if nivel >= 3:
            itens.append(("Administracao (cadastrar funcionarios)", self.tela_cadastro,
                          "Primary.TButton"))
        itens.append(("Sair da conta", self.sair, "Sec.TButton"))
        ttk.Frame(carta).pack(expand=True)  # empurra os botoes para baixo do cartao
        self.grade_botoes(carta, itens, colunas=2)

    def sair(self):
        if self.sessao:
            registrar_evento(self.sessao["usuario"], "Logout")
        self.sessao = None
        self.tela_inicial()

    # ---------- informacoes gerais (todos os niveis) ----------
    def tela_info_geral(self):
        if not self.exigir_sessao(1):
            return
        self.limpar()
        self.titulo("Informacoes gerais", "Conteudo de acesso geral (todos os niveis)")
        carta = self.cartao(lateral=170)
        rodape = ttk.Frame(carta)
        rodape.pack(side="bottom", fill="x")
        self.botao(rodape, "Voltar", self.tela_painel, "Sec.TButton")
        ttk.Label(carta, text="Ministerio do Meio Ambiente", style="Secao.TLabel").pack(
            anchor="w", pady=(0, 8))
        ttk.Label(carta, justify="left", wraplength=700, text=(
            "Informacoes de acesso geral.\n\n"
            "\u2022  Relatorios publicos de fiscalizacao ambiental.\n"
            "\u2022  Calendario de licenciamentos e audiencias publicas.\n"
            "\u2022  Orientacoes de seguranca e uso do sistema de autenticacao.\n\n"
            "Conteudo ilustrativo para fins academicos.")).pack(anchor="w")
        registrar_evento(self.sessao["usuario"], "Consultou informacoes gerais")

    # ---------- cadastro de funcionarios (Ministro) ----------
    def tela_cadastro(self):
        if not self.exigir_sessao(3):
            return
        self.limpar()
        self.titulo("Cadastro de funcionario", "Somente o Ministro pode cadastrar")
        carta = self.cartao(lateral=110, expandir=False)
        grade = self.nova_grade(carta)
        c_nome = self.campo_em(grade, "Nome completo:", 0, 0)
        c_usuario = self.campo_em(grade, "Usuario (3 a 30 caracteres):", 0, 1)
        c_senha = self.campo_em(grade, "Senha (minimo 8 caracteres):", 1, 0, segredo=True)
        c_conf = self.campo_em(grade, "Confirmar senha:", 1, 1, segredo=True)
        quadro = ttk.Frame(grade)
        quadro.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(0, 8))
        ttk.Label(quadro, text="Nivel de acesso:").pack(anchor="w", pady=(0, 3))
        combo = ttk.Combobox(quadro, state="readonly", font=F_TEXTO,
                             values=["1 - Funcionario Geral", "2 - Diretor de Divisao"])
        combo.current(0)
        combo.pack(fill="x")
        ttk.Label(carta, style="Mudo.TLabel", wraplength=760, justify="left", text=(
            "Usuario: letras minusculas, numeros, _ ou -. O nivel 3 (Ministro) nao pode ser "
            "atribuido aqui. O rosto e capturado ANTES de salvar: se o cadastro facial for "
            "cancelado, nada e gravado.")).pack(anchor="w", pady=(2, 0))

        def salvar():
            try:
                nivel = int(combo.get().split(" - ")[0])
                nome, usuario = _validar_dados(c_nome.get(), c_usuario.get(),
                                               c_senha.get(), c_conf.get())
                exigir_nivel(self.usuario_atual(), 3, "cadastrar funcionario")
                self.info("Cadastro facial",
                          "Peca ao funcionario para olhar a camera e mexer levemente a cabeca.")
                amostras = capturar_amostras("Cadastro facial - " + usuario)
                if amostras is None:
                    self.aviso("Cancelado", "Cadastro facial cancelado ou nao concluido. "
                               "Nada foi salvo.")
                    return
                cadastrar_funcionario(self.usuario_atual(), nome, usuario, c_senha.get(),
                                      c_conf.get(), nivel, amostras)
                self.info("Sucesso", "Funcionario cadastrado com rosto.")
                self.tela_funcionarios()
            except Exception as erro:
                self.tratar_erro(erro)

        self.linha_botoes(carta, [("Voltar", self.tela_painel, "Sec.TButton"),
                                  ("Cadastrar rosto e salvar", salvar, "Primary.TButton")])

    # ---------- funcionarios (nivel 2 consulta, nivel 3 administra) ----------
    def tela_funcionarios(self):
        if not self.exigir_sessao(2):
            return
        admin = self.sessao["nivel"] >= 3
        self.limpar()
        self.titulo("Funcionarios cadastrados",
                    "Administracao de contas" if admin else "Somente consulta")
        carta = self.cartao(lateral=36)

        # Itens fixos embaixo (empacotados antes da tabela para nunca ficarem cortados)
        rodape = ttk.Frame(carta)
        rodape.pack(side="bottom", fill="x")
        controles = ttk.Frame(carta)
        if admin:
            controles.pack(side="bottom", fill="x")
        contador = ttk.Label(carta, text="", style="Mudo.TLabel")
        contador.pack(side="bottom", anchor="w", pady=(6, 4))

        tabela = self.criar_tabela(carta, [
            ("nome", "Nome", 230, "w"), ("usuario", "Usuario", 140, "w"),
            ("nivel", "Nivel", 200, "w"), ("status", "Conta", 110, "center"),
            ("rosto", "Rosto", 110, "center")])

        def carregar():
            tabela.delete(*tabela.get_children())
            try:
                lista = listar_funcionarios(self.usuario_atual())
                for posicao, f in enumerate(lista):
                    if f["sem_senha"]:
                        situacao, marca = "Sem senha", "aviso"
                    elif f["bloqueado"]:
                        situacao, marca = "Bloqueada", "alerta"
                    else:
                        situacao, marca = "Ativa", None
                    tags = ("par" if posicao % 2 == 0 else "impar",)
                    if marca:
                        tags = tags + (marca,)
                    tabela.insert("", "end", iid=f["usuario"], tags=tags, values=(
                        f["nome"], f["usuario"], NIVEIS[f["nivel"]], situacao, f["rosto"]))
                contador.config(text="%d funcionario(s) cadastrado(s)" % len(lista))
            except Exception as erro:
                self.tratar_erro(erro)

        def selecionado():
            escolha = tabela.selection()
            if not escolha:
                self.aviso("Selecione", "Selecione um funcionario na tabela.")
                return None
            return escolha[0]

        def remover():
            usuario = selecionado()
            if usuario and self.confirmar(
                    "Confirmar", "Remover %s? O rosto sera guardado em rostos_arquivo." % usuario):
                try:
                    remover_funcionario(self.usuario_atual(), usuario)
                except Exception as erro:
                    self.tratar_erro(erro)
                carregar()

        def desbloquear():
            usuario = selecionado()
            if usuario:
                try:
                    desbloquear_conta(self.usuario_atual(), usuario)
                    self.info("Conta", "Conta desbloqueada.")
                except Exception as erro:
                    self.tratar_erro(erro)
                carregar()

        def redefinir():
            usuario = selecionado()
            if not usuario:
                return
            nova = simpledialog.askstring(
                "Redefinir senha", "Nova senha para %s (minimo 8 caracteres):" % usuario,
                show="*", parent=self.janela)
            if nova is None:
                return
            confirmacao = simpledialog.askstring(
                "Redefinir senha", "Confirme a nova senha:", show="*", parent=self.janela)
            if confirmacao is None:
                return
            try:
                redefinir_senha(self.usuario_atual(), usuario, nova, confirmacao)
                self.info("Senha", "Senha redefinida.")
            except Exception as erro:
                self.tratar_erro(erro)
            carregar()

        def recadastrar():
            usuario = selecionado()
            if not usuario:
                return
            try:
                exigir_nivel(self.usuario_atual(), 3, "recadastrar rosto")
                amostras = capturar_amostras("Recadastro facial - " + usuario)
                if amostras is None:
                    self.aviso("Cancelado", "Operacao cancelada ou nao concluida. "
                               "O rosto anterior foi mantido.")
                    return
                substituir_rosto(self.usuario_atual(), usuario, amostras)
                self.info("Sucesso", "Rosto recadastrado (o anterior foi arquivado).")
            except Exception as erro:
                self.tratar_erro(erro)
            carregar()

        if admin:
            linha_nivel = ttk.Frame(controles)
            linha_nivel.pack(fill="x", pady=(0, 4))
            ttk.Label(linha_nivel, text="Novo nivel para o selecionado:").pack(side="left")
            combo = ttk.Combobox(linha_nivel, state="readonly", font=F_TEXTO, width=26,
                                 values=["1 - Funcionario Geral", "2 - Diretor de Divisao"])
            combo.current(0)
            combo.pack(side="left", padx=10)

            def aplicar_nivel():
                usuario = selecionado()
                if usuario:
                    try:
                        alterar_nivel(self.usuario_atual(), usuario, int(combo.get().split(" - ")[0]))
                    except Exception as erro:
                        self.tratar_erro(erro)
                    carregar()

            ttk.Button(linha_nivel, text="Aplicar nivel ao selecionado", command=aplicar_nivel,
                       style="Primary.TButton").pack(side="left")
            self.grade_botoes(controles, [
                ("Redefinir senha do selecionado", redefinir, "Primary.TButton"),
                ("Recadastrar rosto do selecionado", recadastrar, "Primary.TButton"),
                ("Desbloquear conta do selecionado", desbloquear, "Primary.TButton"),
                ("Remover selecionado", remover, "Danger.TButton")], colunas=2)
        self.botao(rodape, "Voltar", self.tela_painel, "Sec.TButton")
        carregar()

    # ---------- registros (nivel 2 e 3) ----------
    def tela_registros(self):
        if not self.exigir_sessao(2):
            return
        self.limpar()
        self.titulo("Registros de eventos e acessos", "Historico de auditoria (mais recentes primeiro)")
        carta = self.cartao(lateral=36)
        rodape = ttk.Frame(carta)
        rodape.pack(side="bottom", fill="x")
        tabela = self.criar_tabela(carta, [
            ("usuario", "Usuario", 150, "w"), ("evento", "Evento", 460, "w"),
            ("data", "Data e hora", 180, "w")])
        try:
            for posicao, r in enumerate(listar_registros(self.usuario_atual())):
                evento = r["evento"]
                tags = ("par" if posicao % 2 == 0 else "impar",)
                if any(p in evento for p in ("NEGADO", "Falha", "bloqueada", "invalido",
                                             "incorreto", "negado")):
                    tags = tags + ("alerta",)
                elif evento.startswith("Acesso autorizado"):
                    tags = tags + ("ok",)
                tabela.insert("", "end", tags=tags,
                              values=(r["usuario"], evento, r["data_hora"]))
        except Exception as erro:
            self.tratar_erro(erro)
        self.botao(rodape, "Voltar", self.tela_painel, "Sec.TButton")

    # ---------- sobre ----------
    def tela_sobre(self):
        self.limpar()
        self.titulo("Sobre o projeto", "Sistema de Identificacao e Autenticacao Biometrica")
        carta = self.cartao(lateral=150)
        rodape = ttk.Frame(carta)
        rodape.pack(side="bottom", fill="x")
        self.botao(rodape, "Voltar", self.tela_inicial, "Sec.TButton")
        secoes = [
            ("Tema", "Desenvolvimento de um Sistema de Identificacao e Autenticacao Biometrica."),
            ("Objetivo", "Proteger o cofre do Ministerio do Meio Ambiente com senha e "
                         "reconhecimento facial, com tres niveis de acesso."),
            ("Tecnologias", "Python, Tkinter, SQLite, OpenCV (Haar Cascade + LBPH) e NumPy."),
            ("Niveis", "1: Funcionario Geral (informacoes gerais)\n"
                       "2: Diretor de Divisao (+ consulta de funcionarios e registros)\n"
                       "3: Ministro (administracao completa)"),
        ]
        for cabecalho, texto in secoes:
            ttk.Label(carta, text=cabecalho, style="Secao.TLabel").pack(anchor="w", pady=(6, 0))
            ttk.Label(carta, text=texto, justify="left", wraplength=720).pack(anchor="w")
        ttk.Label(carta, text="Aviso importante", style="Erro.TLabel").pack(anchor="w",
                                                                           pady=(10, 0))
        ttk.Label(carta, justify="left", wraplength=720, text=(
            "Solucao DIDATICA. Nao possui prova de vida (liveness): uma foto ou video pode "
            "enganar o reconhecimento facial. A distancia calculada pelo LBPH nao e uma "
            "probabilidade de identidade. NAO deve ser usada para proteger instalacoes ou "
            "informacoes reais.")).pack(anchor="w")


# =========================================================
# INICIALIZACAO
# =========================================================
def _erro_inesperado(tipo, valor, rastro):
    """Evita que um erro dentro de um botao encerre o programa em silencio."""
    messagebox.showerror("Erro inesperado",
                         "Ocorreu um erro inesperado:\n%s\n\nNenhum acesso foi concedido. "
                         "Volte ao inicio e tente novamente." % valor)


def main():
    raiz = tk.Tk()
    raiz.report_callback_exception = _erro_inesperado
    try:
        inicializar_banco()
    except Exception as erro:
        messagebox.showerror("Erro ao iniciar",
                             "Nao foi possivel abrir o banco de dados:\n%s\n\n"
                             "Seus arquivos nao foram apagados." % erro)
        raiz.destroy()
        sys.exit(1)
    try:
        garantir_codigo_inicial()
    except Exception:
        pass  # a tela de configuracao inicial tenta de novo e mostra o erro, se persistir
    Aplicacao(raiz)
    raiz.mainloop()


if __name__ == "__main__":
    main()