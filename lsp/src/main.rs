use std::collections::HashMap;
use std::sync::RwLock;

use clap::Parser;
use fitch_proof;
use tokio;
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

#[derive(Parser)]
struct Args {
    #[arg(long, action)]
    debug: bool,
}

/// by default we use a,b,c for constants and x,y,z for variables
const DEFAULT_ALLOWED_VARIABLE_NAMES: &str = "x,y,z,u,v,w";

#[derive(Debug)]
struct Document {
    text: String,
}

#[derive(Debug)]
struct Backend {
    client: Client,
    documents: RwLock<HashMap<Uri, Document>>,
}

fn location_to_range(span: Option<fitch_proof::Location>) -> Range {
    match span {
        Some(loc) => Range {
            start: Position {
                line: loc.line.saturating_sub(1) as u32,
                character: loc.column.saturating_sub(1) as u32,
            },
            end: Position {
                line: loc.line as u32,
                character: loc.column as u32,
            },
        },

        None => Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 1,
            },
        },
    }
}

fn diagnostic_to_lsp(result: fitch_proof::ProofResult) -> Vec<Diagnostic> {
    fn convert(diag: fitch_proof::Diagnostic, severity: DiagnosticSeverity) -> Diagnostic {
        let fitch_proof::Diagnostic { message, location } = diag;

        Diagnostic {
            range: location_to_range(location),
            severity: Some(severity),
            source: Some("fitchvizier".into()),
            message,
            ..Default::default()
        }
    }

    match result {
        fitch_proof::ProofResult::Correct => vec![],

        fitch_proof::ProofResult::FatalError(diag) => {
            vec![convert(diag, DiagnosticSeverity::ERROR)]
        }

        fitch_proof::ProofResult::Error(diags) => diags
            .into_iter()
            .map(|diag| convert(diag, DiagnosticSeverity::WARNING))
            .collect(),
    }
}

fn end_position(text: &str) -> Position {
    let mut lines = text.split('\n');
    let mut line = 0;
    let mut last = "";

    while let Some(current) = lines.next() {
        last = current;

        if lines.clone().next().is_some() {
            line += 1;
        }
    }

    Position::new(line, last.encode_utf16().count() as u32)
}

impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),

                document_formatting_provider: Some(OneOf::Left(true)),

                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: Some("fitchvizier".into()),
                        inter_file_dependencies: false,
                        workspace_diagnostics: false,
                        ..Default::default()
                    },
                )),

                ..Default::default()
            },

            server_info: Some(ServerInfo {
                name: "fitchvizier-lsp".into(),
                version: None,
            }),

            offset_encoding: None,
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized!")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let doc = params.text_document;

        self.documents
            .write()
            .unwrap()
            .insert(doc.uri, Document { text: doc.text });
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let Some(change) = params.content_changes.into_iter().last() else {
            return;
        };

        self.documents
            .write()
            .unwrap()
            .insert(params.text_document.uri, Document { text: change.text });
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents
            .write()
            .unwrap()
            .remove(&params.text_document.uri);
    }

    async fn diagnostic(
        &self,
        params: DocumentDiagnosticParams,
    ) -> Result<DocumentDiagnosticReportResult> {
        let documents = self.documents.read().unwrap();

        let diagnostics = documents
            .get(&params.text_document.uri)
            .iter()
            .map(|document| {
                fitch_proof::check_proof_diagnostics(&document.text, DEFAULT_ALLOWED_VARIABLE_NAMES)
            })
            .flat_map(diagnostic_to_lsp)
            .collect();

        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,

                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items: diagnostics,
                },
            }),
        ))
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let documents = self.documents.read().unwrap();

        let Some(document) = documents.get(&params.text_document.uri) else {
            return Ok(None);
        };

        let formatted = fitch_proof::format_proof(&document.text);

        if formatted == "invalid" || formatted == document.text {
            return Ok(None);
        }

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position::new(0, 0),
                end: end_position(&document.text),
            },
            new_text: formatted,
        }]))
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend {
        client,
        documents: RwLock::new(HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
